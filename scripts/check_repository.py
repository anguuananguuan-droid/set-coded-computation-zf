#!/usr/bin/env python3
"""Check document paths, session membership, and the independent core boundary.

The proof token scan is deliberately conservative. Isabelle remains the proof
checker. Session parsing covers this repository's plain ROOT theory lists.
"""

from pathlib import Path
import re
import subprocess
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parent.parent
names = subprocess.check_output(
    ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
    cwd=ROOT,
).decode().split("\0")
errors = []
files = sorted({ROOT / name for name in names if name and (ROOT / name).is_file()})
theories = {path for path in files if path.suffix == ".thy"}
members = {}
for directory in (ROOT / "ROOTS").read_text().splitlines():
    if not directory.strip():
        continue
    session_root = ROOT / directory / "ROOT"
    if not session_root.is_file():
        errors.append(f"ROOTS: missing session declaration {directory}/ROOT")
        continue
    source = session_root.read_text()
    blocks = re.findall(r"^  theories\s*\n((?:    \S+[^\n]*\n?)*)", source, re.M)
    for block in blocks:
        for name in block.split():
            path = session_root.parent / f"{name}.thy"
            members.setdefault(path, []).append(directory)
            if path not in theories:
                errors.append(f"{directory}/ROOT: missing public theory {name}")
for path in sorted(theories):
    if len(members.get(path, [])) != 1:
        errors.append(f"{path.relative_to(ROOT)}: expected exactly one session registration")

core = ROOT / "Turing_Machines_ZF/Core"
core_theories = {path.stem for path in theories if path.parent == core}
if not re.search(r"session Set_Coded_Computation_ZF = ZF \+", (core / "ROOT").read_text()):
    errors.append("Core/ROOT: independent session must extend ZF")
for path in sorted(theories):
    source = path.read_text()
    header = re.search(r"\btheory\s+(\w+)\s+imports\s+(.*?)\s+begin\b", source, re.S)
    if not header or header.group(1) != path.stem:
        errors.append(f"{path.relative_to(ROOT)}: theory header does not match filename")
    elif path.parent == core:
        for imported in header.group(2).split():
            if imported.strip('"') not in core_theories | {"ZF", "ZF-Induct.Primrec"}:
                errors.append(f"{path.relative_to(ROOT)}: noncore import {imported}")

for path in files:
    if path.suffix not in {".md", ".txt", ".thy"} and path.name != "README":
        continue
    source = path.read_text()
    relative = path.relative_to(ROOT)
    # Current plain text documents use repository relative paths. Historical
    # Markdown retains document relative links, checked separately below.
    # A source manifest records paths at an older revision, not live links.
    if (path.suffix == ".txt" and not path.name.endswith(".sources.txt")) or path.name == "README":
        for match in re.finditer(
            r"\b(?:Turing_Machines_ZF|Turing_CH|Turing_Models|documentation|papers|scripts)"
            r"/[A-Za-z0-9_./-]+\.(?:thy|txt|md|pdf|py|sh)\b", source
        ):
            if not (ROOT / match.group()).is_file():
                errors.append(f"{relative}: missing source reference {match.group()}")
    if path.suffix == ".thy":
        for match in re.finditer(r"\b(sorry|oops|axiomatization|oracle|skip_proof|quick_and_dirty)\b", source):
            line = source.count("\n", 0, match.start()) + 1
            errors.append(f"{relative}:{line}: proof escape token {match.group()!r}")
        continue
    for match in re.finditer(r"!?\[[^\]\n]*\]\(([^\s)]+)\)", source):
        target = match.group(1).strip("<>")
        url = urlsplit(target)
        if url.scheme or url.netloc or not url.path:
            continue
        destination = path.parent / unquote(url.path)
        if not destination.exists():
            line = source.count("\n", 0, match.start()) + 1
            errors.append(f"{relative}:{line}: missing local link {target}")

if errors:
    raise SystemExit("\n".join(errors))
print(f"Checked {len(theories)} theories in {len(set(d for ds in members.values() for d in ds))} sessions.")
print("Document paths, session membership, core imports, and proof token scan passed.")
