#!/usr/bin/env python3
"""Check the computation dependency closure using only bundled Isabelle/ZF.

The public session has one namespace. This temporary test session checks
its computational sources without AFP; only theory imports are localized.
"""

import argparse
from pathlib import Path
import re
import subprocess

REPOSITORY = Path(__file__).resolve().parent.parent
LEAVES = ("Turing_Examples", "Turing_Instruction_Normalization")
HEADER = re.compile(r"\btheory\s+(\w+)\s+imports\s+(.*?)\s+begin\b", re.S)
TOKENS = re.compile(r'"[^"\n]+"|[\w.]+')
BUNDLED = {"ZF", "ZF-Induct.Primrec"}
ENTRY = "Set_Coded_Turing_Machines"


def theory_catalogue(repository=REPOSITORY):
    sources, owners = {}, {}
    for directory in (repository / "ROOTS").read_text().split():
        declaration = (repository / directory / "ROOT").read_text()
        sessions = re.findall(r"^session\s+(\w+)\s*=", declaration, re.M)
        if len(sessions) != 1:
            raise ValueError(f"Expected one session in {directory}")
        for path in (repository / directory).glob("*.thy"):
            if path.stem in sources:
                raise ValueError(f"Ambiguous theory {path.stem}")
            sources[path.stem] = path
            owners[path.stem] = sessions[0]
    return sources, owners


def project_dependency(name, imported, sources, owners):
    base = imported.rsplit(".", 1)[-1]
    if base not in sources:
        return None
    expected = owners[base]
    if "." in imported and imported.rsplit(".", 1)[0] != expected:
        raise ValueError(f"Wrong session qualifier {imported}, expected {expected}")
    if "." not in imported and owners[name] != expected:
        raise ValueError(f"Cross-session import must be qualified, {name} imports {imported}")
    if owners[name] == ENTRY and expected != ENTRY:
        raise ValueError(f"Canonical entry imports research theory {imported}")
    return base


def computation_sources(repository=REPOSITORY):
    sources, owners = theory_catalogue(repository)
    ordered, active, done = [], set(), set()

    def visit(name):
        if name in done:
            return
        if name in active:
            raise ValueError(f"Cyclic computation import at {name}")
        if name not in sources:
            raise ValueError(f"Missing computation theory {name}")
        active.add(name)
        source = sources[name].read_text()
        header = HEADER.search(source)
        if header is None or header.group(1) != name:
            raise ValueError(f"Invalid computation theory header {name}")
        for token in TOKENS.findall(header.group(2)):
            imported = token.strip('"')
            if imported in BUNDLED:
                continue
            base = project_dependency(name, imported, sources, owners)
            if base is None:
                raise ValueError(f"Nonbundled computation import {imported}")
            visit(base)
        active.remove(name)
        done.add(name)
        ordered.append(sources[name])

    for name in LEAVES:
        visit(name)
    return ordered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--isabelle", required=True, type=Path)
    parser.add_argument("--directory", required=True, type=Path)
    args = parser.parse_args()
    directory = args.directory.resolve()
    if directory.exists():
        raise SystemExit("Use a fresh directory for the independent computation check")
    sources = computation_sources()
    included = {source.stem for source in sources}
    directory.mkdir(parents=True)
    for source in sources:
        text = source.read_text()
        header = HEADER.search(text)
        def localize(match):
            imported = match.group().strip('"')
            base = imported.rsplit(".", 1)[-1]
            return f'"{base}"' if base in included else match.group()
        imports = TOKENS.sub(localize, header.group(2))
        localized = text[:header.start(2)] + imports + text[header.end(2):]
        assert localized[HEADER.search(localized).end():] == text[header.end():]
        (directory / source.name).write_text(localized)
    (directory / "ROOT").write_text(
        "session Computation_ZF_Check = ZF +\n"
        "  options [timeout=300]\n  sessions \"ZF-Induct\"\n  theories\n" +
        "".join(f"    {source.stem}\n" for source in sources))
    print(f"Independent computation check, {len(sources)} theories.", flush=True)
    result = subprocess.run(
        [str(args.isabelle.resolve()), "build", "-v", "-c", "-j", "1",
         "-o", "threads=2", "-D", str(directory)])
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
