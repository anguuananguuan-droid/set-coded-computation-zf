#!/usr/bin/env python3
"""Check a proof PDF using an instrumented copy of its generated LaTeX sources.

The submission document contains no verification code. Instrumentation adds
only log messages to a disposable copy. Its extracted text and geometry must
match the PDF produced by the unmodified submission build.
"""

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import xml.etree.ElementTree as ET


TEXT_BOUNDS = r"""\AtBeginDocument{%
  \typeout{AFP-QA-TEXT-LEFT-SP=\number\dimexpr1in+\hoffset+\oddsidemargin\relax}%
  \typeout{AFP-QA-TEXT-RIGHT-SP=\number\dimexpr1in+\hoffset+\oddsidemargin+\textwidth\relax}%
}
"""


def pdf_pages(pdf, pdftotext):
    result = subprocess.run(
        [pdftotext, "-bbox-layout", str(pdf), "-"], check=True,
        capture_output=True, text=True)
    tree = ET.fromstring(result.stdout)
    pages = tree.findall(".//{*}page")
    if not pages:
        raise ValueError("PDF has no extracted pages")
    return pages


def page_content(pages):
    """Compare page geometry and words without PDF creation-date metadata."""
    return [
        (page.attrib, [(word.attrib, word.text)
                       for word in page.findall(".//{*}word")])
        for page in pages
    ]


def instrument_sources(pdf, sources, qa_dir, isabelle, pdftotext):
    variant = pdf.stem
    root_name = f"root_{variant}" if (sources / f"root_{variant}.tex").is_file() else "root"
    root_file = sources / f"{root_name}.tex"
    source = root_file.read_text(encoding="utf-8")
    if source.count(r"\begin{document}") != 1:
        raise ValueError("Expected one document body in generated LaTeX sources")
    if "AFP-QA-" in source:
        raise ValueError("Unmodified document sources contain verification instrumentation")
    if not (sources / "build").is_file():
        raise ValueError("Generated LaTeX sources are missing their document build script")
    if qa_dir.exists():
        raise ValueError(f"Verification directory already exists, use a fresh path, {qa_dir}")
    if qa_dir == sources or sources in qa_dir.parents or qa_dir == pdf.parent:
        raise ValueError("Verification directory must be separate from the original output")

    compiler = subprocess.run(
        [isabelle, "getenv", "-b", "ISABELLE_LUALATEX"],
        check=True, capture_output=True, text=True).stdout.strip()
    if not compiler:
        raise ValueError("Isabelle has no configured LuaLaTeX command")

    shutil.copytree(sources, qa_dir)
    (qa_dir / f"{root_name}.tex").write_text(
        source.replace(r"\begin{document}", TEXT_BOUNDS + r"\begin{document}"),
        encoding="utf-8")
    environment = dict(os.environ, ISABELLE_LUALATEX=compiler)
    with (qa_dir / "compiler-output.log").open("w", encoding="utf-8") as output:
        subprocess.run(
            ["bash", "build", "pdf", variant], cwd=qa_dir,
            env=environment, stdout=output, stderr=subprocess.STDOUT, check=True)

    original_pages = pdf_pages(pdf, pdftotext)
    checked_pages = pdf_pages(qa_dir / f"{root_name}.pdf", pdftotext)
    if page_content(original_pages) != page_content(checked_pages):
        raise ValueError("Verification copy changed the PDF text or page geometry")
    return qa_dir / f"{root_name}.log", original_pages


def check_document(pdf, log, pdftotext="pdftotext", pages=None):
    source = log.read_text(encoding="utf-8", errors="replace")
    errors = []
    for pattern in (
        r"Overfull \\[hv]box",
        r"LaTeX Warning: (?:Reference|Citation).*undefined",
        r"There were undefined (?:references|citations)",
        r"Label\(s\) may have changed",
        r"Rerun to get (?:cross-references|outlines) right",
    ):
        if re.search(pattern, source):
            errors.append(f"Final LaTeX log contains {pattern}")

    def bound(name):
        values = re.findall(rf"AFP-QA-TEXT-{name}-SP=(\d+)", source)
        if len(values) != 1:
            raise ValueError(f"Expected one declared {name.lower()} text bound")
        return int(values[0]) / 65536 * 72 / 72.27

    left, right = bound("LEFT"), bound("RIGHT")
    if not 0 <= left < right:
        raise ValueError("Invalid declared text bounds")
    if pages is None:
        pages = pdf_pages(pdf, pdftotext)
    words = 0
    for number, page in enumerate(pages, 1):
        if right > float(page.attrib["width"]):
            errors.append(f"Page {number} text bounds exceed paper width")
        for word in page.findall(".//{*}word"):
            words += 1
            xmin, xmax = float(word.attrib["xMin"]), float(word.attrib["xMax"])
            # Allow glyph bearings and extraction rounding, not long formulas.
            if xmin < left - 2 or xmax > right + 2:
                errors.append(
                    f"Page {number} word {word.text!r} at {xmin:.2f}..{xmax:.2f} "
                    f"exceeds text bounds {left:.2f}..{right:.2f}")
    if words == 0:
        errors.append("PDF contains no extracted words")
    if errors:
        raise ValueError("\n".join(errors[:30]))
    return len(pages), words, left, right


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdf", required=True, type=Path)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--log", type=Path, help="Check an existing instrumented final log")
    source.add_argument("--sources", type=Path, help="Generated LaTeX source directory")
    parser.add_argument("--qa-dir", type=Path, help="Fresh verification-copy directory")
    parser.add_argument("--isabelle", default="isabelle", help="Isabelle executable")
    parser.add_argument("--pdftotext", default="pdftotext", help="Poppler executable")
    args = parser.parse_args()
    try:
        pdf = args.pdf.resolve(strict=True)
        pages = None
        log = args.log
        if args.sources:
            if args.qa_dir is None:
                parser.error("--sources requires --qa-dir")
            log, pages = instrument_sources(
                pdf, args.sources.resolve(strict=True), args.qa_dir.resolve(),
                args.isabelle, args.pdftotext)
        elif args.qa_dir is not None:
            parser.error("--qa-dir requires --sources")
        pages, words, left, right = check_document(pdf, log, args.pdftotext, pages)
    except (OSError, ValueError, ET.ParseError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error
    print(f"Checked {args.pdf.name}, {pages} pages, {words} words.")
    print(f"Text bounds {left:.2f}..{right:.2f} pt and final LaTeX log passed.")
    if args.sources:
        print("Verification copy matches the unmodified PDF text and geometry.")


if __name__ == "__main__":
    main()
