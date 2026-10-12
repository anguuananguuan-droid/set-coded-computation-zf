#!/usr/bin/env python3
"""Export the submission manifest from the maintained development theories."""

import argparse
import gzip
from pathlib import Path
import re
import shutil
import tarfile
import tempfile

REPOSITORY = Path(__file__).resolve().parent.parent
ENTRY = "Set_Coded_Halting_Invariance_ZF"


def localize_imports(text, name, sources, included):
    header = re.search(
        rf"^theory\s+{re.escape(name)}\s+imports\s+(.*?)\s+begin\b",
        text, re.M | re.S)
    if header is None:
        raise SystemExit(f"Missing theory header in {name}")

    def localize(match):
        imported = match.group(0).strip('"')
        base = imported.rsplit(".", 1)[-1]
        if base in sources and base not in included:
            raise SystemExit(f"{name} imports excluded theory {imported}")
        if imported.startswith("Set_Coded_Computation_ZF."):
            if base not in sources:
                raise SystemExit(f"{name} imports unknown computation theory {imported}")
            return f'"{base}"'
        return match.group(0)

    imports = re.sub(r'"[^"\n]+"|[\w.]+', localize, header.group(1))
    return text[:header.start(1)] + imports + text[header.end(1):]


def archive_metadata(member):
    member.uid = member.gid = member.mtime = 0
    member.uname = member.gname = ""
    member.mode = 0o755 if member.isdir() or member.mode & 0o111 else 0o644
    member.pax_headers = {}
    return member


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", nargs="?", type=Path,
                        default=REPOSITORY / "output" / f"{ENTRY}.tar.gz")
    args = parser.parse_args()
    manifest = REPOSITORY / "submission" / "ROOT"
    root_text = manifest.read_text()
    block = re.search(r"^  theories\n((?:    \w+\n)+)", root_text, re.M)
    if block is None:
        raise SystemExit("Submission ROOT has no theory list")
    names = block.group(1).split()
    if len(names) != len(set(names)):
        raise SystemExit("Submission ROOT repeats a theory")
    sources = {}
    for directory in (REPOSITORY / "ROOTS").read_text().split():
        for source in (REPOSITORY / directory).glob("*.thy"):
            if source.stem in sources:
                raise SystemExit(f"Ambiguous theory source {source.stem}")
            sources[source.stem] = source
    with tempfile.TemporaryDirectory(prefix="afp-export-") as temporary:
        entry = Path(temporary) / ENTRY
        (entry / "document").mkdir(parents=True)
        for name in names:
            if name not in sources:
                raise SystemExit(f"Missing theory source {name}")
            if sources[name].parent.relative_to(REPOSITORY).as_posix() not in {
                    "thys/Computation", "thys/Invariance"}:
                raise SystemExit(f"Submission includes research theory {name}")
            text = sources[name].read_text(encoding="utf-8")
            # Development sessions share the computation library. The exported
            # entry owns those theories, so its imports are session-local.
            text = localize_imports(text, name, sources, names)
            (entry / f"{name}.thy").write_text(text, encoding="utf-8")
        shutil.copy2(manifest, entry / "ROOT")
        for name in ("root.tex", "build"):
            shutil.copy2(REPOSITORY / "submission/document" / name,
                         entry / "document" / name)
        shutil.copy2(REPOSITORY / "LICENSE", entry / "LICENSE")
        args.archive.parent.mkdir(parents=True, exist_ok=True)
        with args.archive.open("wb") as output:
            with gzip.GzipFile(filename="", mode="wb", fileobj=output, mtime=0) as compressed:
                with tarfile.open(fileobj=compressed, mode="w", format=tarfile.GNU_FORMAT) as archive:
                    for path in [entry, *sorted(entry.rglob("*"))]:
                        relative = path.relative_to(entry.parent)
                        archive.add(path, arcname=str(relative), recursive=False,
                                    filter=archive_metadata)
    print(args.archive.resolve())


if __name__ == "__main__":
    main()
