#!/usr/bin/env python3
"""Export the submission manifest from the maintained development theories."""

import argparse
from pathlib import Path
import re
import shutil
import tarfile
import tempfile

REPOSITORY = Path(__file__).resolve().parent.parent
ENTRY = "Set_Coded_Halting_Invariance_ZF"


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
    for directory in ("Turing_Machines_ZF/Core", "Set_Coded_Invariance_ZF"):
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
            text = sources[name].read_text()
            # Development sessions share the computation library. The exported
            # entry owns those theories, so its imports are session-local.
            text = text.replace('"Set_Coded_Computation_ZF.', '"')
            header = re.search(r"\bimports\s+(.*?)\s+begin\b", text, re.S)
            if header is None:
                raise SystemExit(f"Missing imports in {name}")
            for imported in header.group(1).split():
                imported = imported.strip('"')
                if imported in sources and imported not in names:
                    raise SystemExit(f"{name} imports excluded theory {imported}")
            (entry / f"{name}.thy").write_text(text)
        shutil.copy2(manifest, entry / "ROOT")
        shutil.copy2(REPOSITORY / "submission/document/root.tex",
                     entry / "document/root.tex")
        shutil.copy2(REPOSITORY / "LICENSE", entry / "LICENSE")
        args.archive.parent.mkdir(parents=True, exist_ok=True)
        with tarfile.open(args.archive, "w:gz") as archive:
            archive.add(entry, arcname=ENTRY)
    print(args.archive.resolve())


if __name__ == "__main__":
    main()
