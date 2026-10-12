#!/usr/bin/env python3
"""Verify that the AFP linter accepts a clean theory and rejects violations.

The deliberately invalid theories exist only in a temporary directory.
quick_and_dirty is enabled only for the unfinished-proof control, so that
the linter, rather than Isabelle's proof admission check, must reject it.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile


CASES = (
    ("Clean", 'lemma reflexive: "x = x" by simp\n', None, False),
    ("Unnamed", 'lemma [simp]: "x = x" by simp\n',
     "global_attribute_on_unnamed_lemma", False),
    ("Unfinished", 'lemma unfinished: "A \\<subseteq> A"\n  sorry\n',
     "unfinished_proof", True),
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--isabelle", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    executable = args.isabelle.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    results = []
    failures = []
    with tempfile.TemporaryDirectory(prefix="afp-linter-controls-") as temporary:
        for name, body, expected, admit in CASES:
            directory = Path(temporary) / name
            directory.mkdir()
            session = f"AFP_Linter_Control_{name}"
            theory = f"Linter_Control_{name}"
            source = f"theory {theory} imports ZF begin\n{body}end\n"
            (directory / "ROOT").write_text(
                f"session {session} = ZF +\n"
                f"  options [timeout=300]\n  theories {theory}\n")
            (directory / f"{theory}.thy").write_text(source)
            report = output / f"{name.lower()}.txt"
            # A stale successful report must not conceal a failed invocation.
            report.unlink(missing_ok=True)
            command = [str(executable), "lint", "-c", "-v", "-j", "1",
                       "-o", "threads=2", "-o", "lint_bundles=afp_mandatory",
                       "-f", "error", "-O", str(report), "-D", str(directory)]
            if admit:
                command.extend(["-o", "quick_and_dirty=true"])
            result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, timeout=360)
            (output / f"{name.lower()}.log").write_text(result.stdout)
            text = report.read_text() if report.is_file() else None
            covered = re.search(
                rf"Parsed ([1-9][0-9]*) commands in {session}\.{theory}\b",
                result.stdout)
            if expected is None:
                passed = result.returncode == 0 and text == "" and covered is not None
            else:
                passed = (result.returncode != 0 and text is not None and
                          f"[{expected}]" in text and covered is not None)
            results.append({"case": name, "source": source, "command": command,
                            "exit_code": result.returncode,
                            "parsed_commands": int(covered.group(1)) if covered else 0,
                            "expected_lint": expected, "passed": passed})
            print(f"{name}, exit {result.returncode}, "
                  f"{'passed' if passed else 'FAILED'}", flush=True)
            if not passed:
                failures.append(name)
    (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    if failures:
        raise SystemExit("AFP linter controls failed, " + ", ".join(failures))


if __name__ == "__main__":
    main()
