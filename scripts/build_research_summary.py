#!/usr/bin/env python3
"""Build the one-page public research summary. Requires reportlab and pypdf."""

from pathlib import Path
import re

from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.units import mm
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import SimpleDocTemplate, Paragraph, KeepTogether
from pypdf import PdfReader


OUT = Path(__file__).resolve().parents[1] / "papers"
OUT.mkdir(parents=True, exist_ok=True)
PDF = OUT / "Research_Summary.pdf"


def serif_fonts():
    candidates = [
        (
            Path("/System/Library/Fonts/Supplemental"),
            ("Times New Roman.ttf", "Times New Roman Bold.ttf"),
        ),
        (
            Path("/usr/share/fonts/truetype/liberation2"),
            ("LiberationSerif-Regular.ttf", "LiberationSerif-Bold.ttf"),
        ),
        (
            Path("/usr/share/fonts/truetype/liberation"),
            ("LiberationSerif-Regular.ttf", "LiberationSerif-Bold.ttf"),
        ),
    ]
    for directory, filenames in candidates:
        paths = [directory / filename for filename in filenames]
        if all(path.exists() for path in paths):
            for face, path in zip(("ResearchSerif", "ResearchSerifBold"), paths):
                pdfmetrics.registerFont(TTFont(face, str(path)))
            return "ResearchSerif", "ResearchSerifBold"
    return "Times-Roman", "Times-Bold"


SERIF, SERIF_BOLD = serif_fonts()
mono_path = Path("/System/Library/Fonts/Supplemental/Courier New.ttf")
if mono_path.exists():
    pdfmetrics.registerFont(TTFont("ResearchMono", str(mono_path)))
    MONO = "ResearchMono"
else:
    MONO = "Courier"

STYLES = {
    "title": ParagraphStyle(
        "title", fontName=SERIF_BOLD, fontSize=19, leading=23,
        textColor=colors.black, spaceAfter=9,
    ),
    "author": ParagraphStyle(
        "author", fontName=SERIF, fontSize=10.5, leading=15,
        spaceAfter=19,
    ),
    "heading": ParagraphStyle(
        "heading", fontName=SERIF_BOLD, fontSize=11.2, leading=14,
        spaceBefore=10.5, spaceAfter=4,
    ),
    "body": ParagraphStyle(
        "body", fontName=SERIF, fontSize=11.2, leading=15.1,
        alignment=TA_LEFT, spaceAfter=2,
    ),
    "equation": ParagraphStyle(
        "equation", fontName=MONO, fontSize=9.1, leading=13.5,
        leftIndent=12, spaceBefore=7, spaceAfter=8,
    ),
    "links": ParagraphStyle(
        "links", fontName=SERIF, fontSize=9, leading=13,
        spaceBefore=11,
    ),
}

REPO = "https://github.com/anguuananguuan-droid/set-coded-computation-zf"
REV = "6c1b42c9e853ff61e934ce08b1e4a40c60166fa3"
THEOREM = f"{REPO}/blob/{REV}/thys/Set_Coded_Turing_Machines/Turing_Halting_Sentences.thy#L192"
CI = f"{REPO}/actions/runs/38594422660"
EPQ = f"{REPO}/blob/{REV}/papers/EPQ.pdf"

SECTIONS = [
    (
        "1 Research question",
        "An EPQ investigation of the continuum hypothesis and the computability of "
        "model invariance motivated this development. The formalisation requires "
        "a precise connection between external computation and truth inside "
        "set-theoretic models. The library defines deterministic Turing machines "
        "as sets, their finite execution, numerical machine encodings, and tape "
        "equivalence that ignores surplus blank cells.",
    ),
    (
        "2 Verified connection",
        "For each well-formed machine P and finite symbol input x, the construction "
        "halt_sentence(P,x) is an explicit first-order sentence with no free "
        "variables. For every transitive ZF set model M, the following equivalence "
        "is proved.",
    ),
    (
        "3 Effective sentence construction",
        "For independently supplied natural numbers e and n, a primitive-recursive "
        "constructor returns the exact code of "
        "halt_sentence(decode_machine(e),numeral_input(n)). Both membership in the "
        "primitive-recursive class and equality to this formula code are proved. "
        "The self-input case takes n equal to e. The certificate concerns numerical "
        "construction.",
    ),
    (
        "4 Use, verification and scope",
        "The standalone AFP candidate contains 17 theories. Client examples derive "
        "program properties, transfer them across equivalent tapes, and obtain "
        "model-satisfaction statements through named interfaces. The recorded "
        "GitHub Actions build checks the candidate and separate research sessions "
        "with Isabelle2025-2 and the AFP snapshot of 6 October 2026. Research extensions "
        "remain separate, and the full EPQ argument is not yet formalised. The "
        "candidate has not been submitted to or accepted by AFP.",
    ),
]


def para(text, style="body"):
    return Paragraph(text, STYLES[style])


def footer(canvas, doc):
    canvas.saveState()
    canvas.setStrokeColor(colors.black)
    canvas.setLineWidth(0.35)
    canvas.line(25 * mm, 20.5 * mm, A4[0] - 25 * mm, 20.5 * mm)
    canvas.setFont(SERIF, 8.3)
    canvas.drawString(25 * mm, 16 * mm, "Research summary. Source revision 6c1b42c.")
    canvas.drawRightString(A4[0] - 25 * mm, 16 * mm, "1")
    canvas.restoreState()


doc = SimpleDocTemplate(
    str(PDF), pagesize=A4, leftMargin=25 * mm, rightMargin=25 * mm,
    topMargin=22 * mm, bottomMargin=26 * mm,
    title="Set-Coded Turing Machines in Isabelle/ZF",
    author="Tang Ziyi", subject="Formal machine execution and halting in transitive ZF models",
    creator="Research summary build script, ReportLab",
)

story = [
    para("Set-Coded Turing Machines in Isabelle/ZF", "title"),
    para("Tang Ziyi<br/>2 November 2026", "author"),
]

for number, (heading, text) in enumerate(SECTIONS, start=1):
    block = [para(heading, "heading"), para(text)]
    if number == 2:
        block.extend([
            para("M satisfies halt_sentence(P,x) iff P halts on x.", "equation"),
            para(
                "The sentence depends only on P and x. A finite halting trace "
                "provides an internal witness, and an internal witness determines "
                "the corresponding external finite execution. Model existence is "
                "not asserted."
            ),
        ])
    story.append(KeepTogether(block))

story.append(para(
    f'<link href="{REPO}" color="black"><u>Repository</u></link>'
    f' &nbsp; | &nbsp; <link href="{THEOREM}" color="black"><u>Main theorem</u></link>'
    f' &nbsp; | &nbsp; <link href="{CI}" color="black"><u>Recorded build</u></link>'
    f' &nbsp; | &nbsp; <link href="{EPQ}" color="black"><u>EPQ paper</u></link>'
    '<br/>github.com/anguuananguuan-droid/set-coded-computation-zf',
    "links",
))

doc.build(story, onFirstPage=footer, onLaterPages=footer)
reader = PdfReader(str(PDF))
if len(reader.pages) != 1:
    raise RuntimeError(f"Expected one page, got {len(reader.pages)}")
extracted = "\n".join(page.extract_text() or "" for page in reader.pages)
word_count = len(re.findall(r"\b[\w'-]+\b", extracted))
if word_count > 450:
    raise RuntimeError(f"Expected at most 450 words, got {word_count}")
links = []
for page in reader.pages:
    for annotation in page.get("/Annots", []):
        action = annotation.get_object().get("/A", {})
        if "/URI" in action:
            links.append(str(action["/URI"]))
if links != [REPO, THEOREM, CI, EPQ]:
    raise RuntimeError(f"Unexpected link targets: {links}")
print(f"Created {PDF}. Pages 1. Extracted words {word_count}. Link targets 4.")
