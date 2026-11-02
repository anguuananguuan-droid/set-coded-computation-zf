#!/usr/bin/env python3
"""Extract the candidate's completed EPQ sections without changing their pages.

Requires pypdf. The complete public form remains the source document.
"""

from hashlib import sha256
from pathlib import Path

from pypdf import PdfReader, PdfWriter


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "papers/EPQ_Production_Log.pdf"
OUTPUT = ROOT / "papers/EPQ_Log.pdf"
SOURCE_SHA256 = "cfc62c03c5af4c16d06da4be75c0fb02f5b77f189f66539ba0942414770945f7"
PAGES = (7, 8, 9, 10, 14, 15, 16, 17, 18, 19, 22, 23)
SECTIONS = (
    ("Record of initial ideas", 7),
    ("Candidate proposal", 10),
    ("Planning review", 14),
    ("Mid-project review", 15),
    ("Project product review", 17),
    ("Presentation record", 18),
    ("Summary and reflection", 22),
)


def main():
    if sha256(SOURCE.read_bytes()).hexdigest() != SOURCE_SHA256:
        raise RuntimeError("The source form changed; review the page selection first.")
    reader = PdfReader(SOURCE)
    if len(reader.pages) != 24:
        raise RuntimeError("Expected the recorded 24-page source form.")

    writer = PdfWriter()
    writer.append(reader, pages=[page - 1 for page in PAGES], import_outline=False)
    writer.add_metadata({
        "/Title": "EPQ Production Log",
        "/Author": "Tang Ziyi",
        "/Subject": "Reading copy of completed candidate sections. Original pages "
                    "7–10, 14–19, 22–23. Original wording and page numbers retained.",
    })
    for title, original_page in SECTIONS:
        writer.add_outline_item(title, PAGES.index(original_page))
    with OUTPUT.open("wb") as stream:
        writer.write(stream)

    result = PdfReader(OUTPUT)
    if len(result.pages) != len(PAGES):
        raise RuntimeError("The reading copy has an unexpected page count.")
    for page, original_page in zip(result.pages, PAGES):
        original = reader.pages[original_page - 1]
        if page.extract_text() != original.extract_text():
            raise RuntimeError(f"Text changed on source page {original_page}.")
        if page.get_contents().get_data() != original.get_contents().get_data():
            raise RuntimeError(f"Page content changed on source page {original_page}.")
        if any(abs(float(a) - float(b)) > 0.00001
               for a, b in zip(page.mediabox, original.mediabox)):
            raise RuntimeError(f"Page dimensions changed on source page {original_page}.")
    if "Record of initial ideas" not in (result.pages[0].extract_text() or ""):
        raise RuntimeError("The reading copy does not start with the research narrative.")
    print(f"Created {OUTPUT}. Pages 12. Text and page streams unchanged; dimensions preserved.")


if __name__ == "__main__":
    main()
