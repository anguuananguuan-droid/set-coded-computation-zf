#!/usr/bin/env python3
"""Check document paths, session membership, and the computation dependency boundary.

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
directories = (ROOT / "ROOTS").read_text().splitlines()
if len(directories) != len(set(directories)):
    errors.append("ROOTS: repeated session directory")
for directory in directories:
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

from check_computation import computation_sources, theory_catalogue, project_dependency
try:
    catalogue, owners = theory_catalogue(ROOT)
    computation_sources(ROOT)
except ValueError as error:
    errors.append(str(error))
canonical = ROOT / "thys/Set_Coded_Halting_Invariance_ZF"
canonical_names = {p.stem for p in theories if p.parent == canonical}
for path in sorted(theories):
    source = path.read_text()
    header = re.search(r"\btheory\s+(\w+)\s+imports\s+(.*?)\s+begin\b", source, re.S)
    file_header = re.match(r"\(\*.*?\*\)", source, re.S)
    fields = file_header.group() if file_header else ""
    if not re.search(rf"\bTitle:\s+{re.escape(path.name)}\b", fields):
        errors.append(f"{path.relative_to(ROOT)}: missing matching Title in file header")
    if not re.search(r"\bAuthor:\s+\S", fields):
        errors.append(f"{path.relative_to(ROOT)}: missing Author in file header")
    if len(re.findall(r"^section\s", source, re.M)) != 1:
        errors.append(f"{path.relative_to(ROOT)}: expected one theory-level section")
    if not header or header.group(1) != path.stem:
        errors.append(f"{path.relative_to(ROOT)}: theory header does not match filename")
    else:
        for imported in re.findall(r'"[^"\n]+"|[\w.]+', header.group(2)):
            try:
                project_dependency(path.stem, imported.strip('"'), catalogue, owners)
            except ValueError as error:
                errors.append(f"{path.relative_to(ROOT)}: {error}")

for path in files:
    if path.suffix not in {".md", ".txt", ".thy"} and path.name != "README":
        continue
    source = path.read_text()
    relative = path.relative_to(ROOT)
    # Historical records describe their original source revision. Current
    # plain text documents use live repository-relative paths. Markdown link
    # destinations are live navigation, including those in historical prose.
    historical = relative.parts[:2] in {
        ("documentation", "records"), ("documentation", "history")}
    if not historical and (path.suffix == ".txt" or path.name == "README"):
        for match in re.finditer(
            r"\b(?:thys|submission|documentation|papers|scripts)"
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
print("Document paths, session membership, file headers, computation imports, and proof token scan passed.")
