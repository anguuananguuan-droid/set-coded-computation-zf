# Set coded computation in Isabelle/ZF

Tang Ziyi

## 1 Computation

This development represents a Turing machine, its tape, and each finite run
as sets in Isabelle/ZF. It defines execution from a finite instruction table
and proves that no machine in this model can decide, for every input code,
whether the encoded machine halts on that same code.

The independent library also gives a natural number encoding of machines and
configurations, with a numeric evaluator proved to reproduce execution.
Operations on codes and finite-step evaluation have primitive-recursive
certificates in Isabelle/ZF.
Two further results concern the finite representation of the tape. Adding
trailing blanks preserves its observed contents, and a supplied blank buffer
protects saved data during a bounded number of steps.

[Computation in Isabelle/ZF](documentation/COMPUTATION.md) explains the model
through a small machine, then develops the coding, diagonal argument, and
tape results. Each result is linked to its source. The eleven theory files
form the session
[Set_Coded_Computation_ZF](Turing_Machines_ZF/Core/ROOT), which depends only
on Isabelle/ZF and its bundled ZF-Induct session.

## 2 Effective syntax and invariance

The [Set_Coded_Invariance_ZF](Set_Coded_Invariance_ZF/ROOT) session extends
the computation library and uses the AFP entry Independence_CH. It constructs
closed formulas for machine halting and proves that their satisfaction in
every transitive ZFC set model agrees with external finite execution. It
also defines an injective numerical code for formulas and gives
primitive-recursive functions that produce the codes of a halting sentence
or its negation, each disjoined with CH.

If a countable transitive ZFC set model exists, both self-input halting and
its complement primitive-recursively many-one reduce to the set of codes of
sentences invariant across all transitive ZFC set models. The model
existence hypothesis is necessary for the CH disagreement used in the
reductions. This result does not require a compiler from arbitrary primitive
recursive functions to the Turing machines defined here.

## 3 Verification

With Isabelle2025-2 on the executable search path, run from the repository
root.

```sh
isabelle build -v -D Turing_Machines_ZF/Core Set_Coded_Computation_ZF
```

[Build instructions](documentation/BUILD.txt) specify the environment and
commands for the independent library, the invariance session, and the complete
repository. [AFP candidates](documentation/AFP.txt) record the two submission
scopes and their dependency.
[GitHub Actions](https://github.com/anguuananguuan-droid/set-coded-computation-zf/actions/workflows/isabelle.yml)
checks the independent library and all five project sessions. Each run
identifies the source revision and retains its build logs.

## 4 Further research

The remaining theories contain concrete programs, primitive recursive
certificates, and arithmetic satisfaction lemmas. The general machine
compiler, a universal machine implementing the numeric evaluator, and an
effective translation of arbitrary arithmetic sentences remain unfinished.
The effective reduction from arithmetic truth and the nonarithmeticality
conclusion in the motivating [EPQ paper](papers/EPQ.pdf) are not established
by the self-halting reductions proved here.

[Research extensions](documentation/RESEARCH.md) records their results and
open obligations. [Development records](documentation/history/README.md)
preserve earlier reviews and verification evidence.

## 5 Attribution

Tang Ziyi formulated the research question and wrote the original EPQ argument
and initial formalisation. Subsequent definitions, proofs, and repository
engineering include substantial AI assistance, described in
[AI assistance](AI_USAGE.txt).

The five action machine model follows the operational design of the AFP entry
[Universal Turing Machine](https://www.isa-afp.org/entries/Universal_Turing_Machine.html),
formalised in Isabelle/HOL. The present development proves its results in
Isabelle/ZF. Its scope and dependencies are described in the computation note.

Sources and documentation use the [BSD 3 Clause License](LICENSE).
The EPQ paper is copyright 2026 Tang Ziyi, all rights reserved.
[Citation metadata](CITATION.cff) identifies the repository. Cite the source
revision used.
