#!/usr/bin/env python3
"""Apply the local Isabelle2025-2 compatibility patch to a pinned linter.

Upstream is isabelle-prover/isabelle-linter at
c9983adc5c51a6455f702bb58c9f960d425a2af3, distributed under its MIT license.
The local patch handles exported command_range wrappers, rejects theories
with no parsed commands, and records command coverage in verbose output.
Only the two expected upstream files are changed. Unknown inputs are rejected.
"""

import argparse
import hashlib
from pathlib import Path
import subprocess


CHECKSUMS = {
    "linter_base/src/token_markup.scala": (
        "38fd0b84e055ad591cdf9740164c666ad1edc5fc74ef163fd6bf5e0032c897e5",
        "89d02c5b612a0153f2145b013366ac0f844565dffc13e894c067844db31ad34d",
    ),
    "linter_base/src/linter.scala": (
        "45eb75b358a8f1fc3a1e69ed17cdcf42bc4a7cca64f0961c1699761c6beb8b85",
        "8fcfc2cbd622f87b3b81f9c13a0c1b1acc0e9476788704d978d237a491cdbcf4",
    ),
}
PATCH_SHA256 = "0f3f0dad101a3d5dbe3f0986a38de7c1b06d1ba5ef134882ec7ab0005d68527b"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("component", type=Path)
    component = parser.parse_args().component.resolve()
    patch = Path(__file__).with_name("isabelle-linter-2025-2.patch")
    if sha256(patch) != PATCH_SHA256:
        raise SystemExit("Unexpected local linter patch checksum")
    states = []
    for name, (upstream, patched) in CHECKSUMS.items():
        digest = sha256(component / name)
        if digest == upstream:
            states.append("upstream")
        elif digest == patched:
            states.append("patched")
        else:
            raise SystemExit(f"Unexpected pinned linter source checksum, {name}")
    if all(state == "patched" for state in states):
        print("Verified local linter compatibility patch")
        return
    if not all(state == "upstream" for state in states):
        raise SystemExit("Partially patched linter sources, use a fresh extraction")
    subprocess.run(["patch", "-p1", "-i", str(patch)], cwd=component,
                   check=True, stdin=subprocess.DEVNULL)
    for name, (_, patched) in CHECKSUMS.items():
        if sha256(component / name) != patched:
            raise SystemExit(f"Linter patch verification failed, {name}")
    print("Applied and verified local linter compatibility patch")


if __name__ == "__main__":
    main()
