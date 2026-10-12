#!/usr/bin/env python3
"""Check a proof PDF against its final LaTeX log and declared text bounds."""

import argparse
from pathlib import Path
import re
import subprocess
import xml.etree.ElementTree as ET


def check_document(pdf, log):
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
    result = subprocess.run(
        ["pdftotext", "-bbox-layout", str(pdf), "-"], check=True,
        capture_output=True, text=True)
    tree = ET.fromstring(result.stdout)
    pages = tree.findall(".//{*}page")
    if not pages:
        raise ValueError("PDF has no extracted pages")
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
    parser.add_argument("--log", required=True, type=Path)
    args = parser.parse_args()
    try:
        pages, words, left, right = check_document(args.pdf, args.log)
    except (ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error
    print(f"Checked {args.pdf.name}, {pages} pages, {words} words.")
    print(f"Text bounds {left:.2f}..{right:.2f} pt and final LaTeX log passed.")


if __name__ == "__main__":
    main()
