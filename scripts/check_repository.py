#!/usr/bin/env python3
"""Check public Markdown links and reject proof escapes in project theories."""

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
for path in files:
    if path.suffix not in {".md", ".thy"}:
        continue
    source = path.read_text()
    relative = path.relative_to(ROOT)
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
print("Public Markdown links and theory proof-escape scan passed.")
