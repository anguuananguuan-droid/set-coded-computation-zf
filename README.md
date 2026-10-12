# Halting absoluteness and effective sentence invariance in Isabelle/ZF

Tang Ziyi

## 1 Result

This development constructs a set-theoretic formula for machine halting and
proves that its satisfaction in every transitive ZF set model agrees with
external finite execution. The machine and its input are then named inside
closed sentences. These results do not require the axiom of choice.

Assuming a countable transitive ZFC set model exists, two explicit
primitive-recursive maps reduce self-input halting and its complement to the
natural-number codes of sentences invariant across all transitive ZFC set
models. CH supplies a sentence on which two such models disagree. The
reductions also hold under the direct premise that CH is not invariant.

The two maps are proved members of Isabelle/ZF's `prim_rec` class, with
application equations identifying their outputs with the intended sentence
codes. The source halting set is proved undecidable in the machine model.
The development does not establish machine undecidability of the full target
set or a general compiler implementing arbitrary primitive-recursive maps.

The sole AFP candidate is
[Set_Coded_Halting_Invariance_ZF](thys/Set_Coded_Halting_Invariance_ZF/ROOT).
Its nineteen maintained theories and its ROOT are exported unchanged into
one session with
[Independence_CH](https://isa-afp.org/entries/Independence_CH.html) as its parent.
[Candidate scope](documentation/AFP.txt) states its theorem, boundaries, and
verification procedure. The entry has not been submitted or accepted.

## 2 Sources

The repository maintains forty theories in five sessions. The candidate
has one source directory and one public theory namespace. Research sessions
extend it through that namespace.

```text
thys/Set_Coded_Halting_Invariance_ZF   19 theories, candidate
thys/Research/Computation              4 theories, tape and evaluation
thys/Research/Programs                14 theories, machine programs
thys/Research/Models                   2 theories, arithmetic and model index sets
thys/Research/Absoluteness             1 theory, decidable sets in models
```

[Computation](documentation/COMPUTATION.md) describes machine semantics,
coding, numeric evaluation, self-halting undecidability, observational tape
semantics, and bounded workspace preservation.
[Theory guide](documentation/RESEARCH.md) locates the forty theories and their
proved and open boundaries.

The general machine compiler, a universal machine implementing the numeric
evaluator, and an effective translation of arbitrary arithmetic sentences
remain open. The arithmetic-truth reduction and nonarithmeticality conclusion
of the motivating [EPQ paper](papers/EPQ.pdf) are not established by the
self-halting reductions.

## 3 Reproduction

With Isabelle2025-2 installed, check the computation fragment independently
of AFP. This command generates a temporary verification session from the
maintained sources.

```sh
python3 scripts/check_computation.py --isabelle /absolute/path/to/isabelle --directory output/computation-check
```

[Build instructions](documentation/BUILD.txt) cover the five sessions,
exported archive, proof dependencies, PDF layout, and style checks. Style
acceptance requires the pinned linter with its maintained compatibility patch
and negative controls demonstrating detection of deliberate violations.
An empty linter report alone is insufficient evidence.

[GitHub Actions](https://github.com/anguuananguuan-droid/set-coded-computation-zf/actions/workflows/isabelle.yml)
retains the checked source revision, exported archive, document variants, and
verification logs. A successful run verifies that revision. Mathematical
adequacy and AFP acceptance require separate review.

## 4 Attribution and maintenance

Tang Ziyi formulated the research question and wrote the original EPQ
argument and initial formalisation. Subsequent definitions, proofs, and
repository engineering include substantial AI assistance, recorded in
[AI assistance](AI_USAGE.txt).

The operational machine design follows
[Universal Turing Machine](https://isa-afp.org/entries/Universal_Turing_Machine.html),
formalised in Isabelle/HOL. The model and proofs here use Isabelle/ZF.
Model closure and satisfaction use
[Transitive Models of Fragments of ZFC](https://isa-afp.org/entries/Transitive_Models.html).

The Isabelle theories and project documentation use the
[BSD 3 Clause License](LICENSE).
The linter patch retains the upstream
[copyright and license notice](THIRD_PARTY_NOTICES.txt).
The EPQ paper is copyright 2026 Tang Ziyi, all rights reserved.
[Citation metadata](CITATION.cff) identifies the project. Cite the revision
used. [Contribution rules](CONTRIBUTING.txt) and [engineering rules](AGENTS.md)
govern changes. [Development records](documentation/history/README.md)
preserve earlier claims and verification evidence at their recorded revisions.
