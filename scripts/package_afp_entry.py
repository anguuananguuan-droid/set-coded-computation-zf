#!/usr/bin/env python3
"""Archive the canonical AFP session without rewriting its source files."""

import argparse
import gzip
from pathlib import Path
import re
import shutil
import tarfile
import tempfile

REPOSITORY = Path(__file__).resolve().parent.parent
ENTRY = "Set_Coded_Halting_Invariance_ZF"
SOURCE = REPOSITORY / "thys" / ENTRY


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
    manifest = SOURCE / "ROOT"
    block = re.search(r"^  theories\n((?:    \w+\n)+)", manifest.read_text(), re.M)
    if block is None:
        raise SystemExit("Canonical ROOT has no theory list")
    names = block.group(1).split()
    if len(names) != len(set(names)):
        raise SystemExit("Canonical ROOT repeats a theory")
    if set(names) != {path.stem for path in SOURCE.glob("*.thy")}:
        raise SystemExit("Canonical theory files and ROOT membership differ")
    with tempfile.TemporaryDirectory(prefix="afp-export-") as temporary:
        entry = Path(temporary) / ENTRY
        (entry / "document").mkdir(parents=True)
        for name in names:
            shutil.copy2(SOURCE / f"{name}.thy", entry / f"{name}.thy")
        shutil.copy2(manifest, entry / "ROOT")
        for name in ("root.tex", "build"):
            shutil.copy2(SOURCE / "document" / name, entry / "document" / name)
        shutil.copy2(REPOSITORY / "LICENSE", entry / "LICENSE")
        args.archive.parent.mkdir(parents=True, exist_ok=True)
        with args.archive.open("wb") as output:
            with gzip.GzipFile(filename="", mode="wb", fileobj=output, mtime=0) as compressed:
                with tarfile.open(fileobj=compressed, mode="w", format=tarfile.GNU_FORMAT) as archive:
                    for path in [entry, *sorted(entry.rglob("*"))]:
                        archive.add(path, arcname=str(path.relative_to(entry.parent)),
                                    recursive=False, filter=archive_metadata)
    print(args.archive.resolve())


if __name__ == "__main__":
    main()
