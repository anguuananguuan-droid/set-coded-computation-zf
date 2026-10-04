# Set-Coded Computation in Isabelle/ZF

[![Isabelle build](https://github.com/anguuananguuan-droid/set-coded-computation-zf/actions/workflows/isabelle.yml/badge.svg)](https://github.com/anguuananguuan-droid/set-coded-computation-zf/actions/workflows/isabelle.yml)
[![Isabelle2025-2](https://img.shields.io/badge/Isabelle-2025--2-5c6b80)](https://isabelle.in.tum.de/website-Isabelle2025-2/)

**Tang Ziyi · Computability and set theory**

A formal study of binary Turing machines inside Zermelo–Fraenkel set theory.
The project starts with finite instruction tables and works toward a connection
between machine execution and truth across transitive models of ZFC.

It grew out of an [EPQ paper](papers/EPQ.pdf) about mathematical discovery and
model invariance. The paper's final argument is the research target; its full
formalisation remains open.

## Results

All machine definitions and proofs use **Isabelle/ZF**, with a single tape,
a binary alphabet, and finite deterministic control.

| Result | Where to look |
| :--- | :--- |
| Natural-number machine coding and a numeric evaluator with exact simulation theorems | [Coding](Turing_Machines_ZF/Turing_Coding.thy) · [Evaluation](Turing_Machines_ZF/Turing_Evaluator.thy) |
| Self-input halting is undecidable, proved using a concrete machine transformation | [Transformations](Turing_Machines_ZF/Turing_Transformations.thy) |
| Concrete copying, addition, constants, successor, and arbitrary projections | [Arithmetic](Turing_Machines_ZF/Turing_Arithmetic.thy) · [Realisation](Turing_Machines_ZF/Turing_Realisation.thy) |
| Arbitrary finite executions can be isolated from saved data by explicit blank buffers | [Workspace preservation](Turing_Machines_ZF/Turing_Workspace.thy) |
| Every transitive ZFC set model contains the machines, configurations, and finite halting certificates | [Model witnesses](Turing_Models/Turing_Model_Witnesses.thy) |
| Natural-number domain, zero, successor, order, addition, multiplication, and restricted quantifiers have verified model satisfaction rules | [Arithmetic formulas](Turing_Models/Turing_Arithmetic_Truth.thy) |
| A uniform-truth sentence, disjoined with a fixed non-invariant sentence, tests invariance | [CH application](Turing_CH/Turing_CH.thy) |

The source contains no `sorry`, added axioms, or custom proof oracles. The
[build workflow](.github/workflows/isabelle.yml) checks the repository against
fixed Isabelle and AFP releases.

## Two issues the formalisation exposed

**A finite list is not the tape itself.** An earlier numerical-output contract
required literal equality of finite lists. Since the machine cannot delete
represented cells, that contract ruled out every output shorter than its input.
The repaired definition compares tape contents, treating unrepresented cells
as blank. It supports erasure and preserves the head-alignment requirement.
See [tape equivalence](Turing_Machines_ZF/Turing_Tape.thy).

**Correct output does not guarantee safe storage.** A program can compute
identity on an otherwise blank tape and still erase data placed to its left.
The [counterexample](Turing_Machines_ZF/Turing_Context.thy) explains why general
function composition needs an additional storage argument. The new workspace
theorem proves that `n` blank cells on each side protect arbitrary saved data
through every prefix of an `n`-step execution. The time bound is supplied;
it is not a procedure for predicting when a program halts.

## Connection to the EPQ

Assuming a countable transitive model of ZFC exists, the intended endpoint is
a many-one reduction from true arithmetic to the codes of sentences invariant
across transitive ZFC set models. This would establish that the invariant-sentence
index set is not arithmetical.

The current development proves the semantic disjunction principle and uses
AFP's CH independence results to obtain a non-invariant sentence, assuming a
countable transitive model of ZFC exists. It now also proves that finite
computation witnesses belong to every such transitive model. A direct arithmetic
route has begun with satisfaction rules for the natural-number domain, basic
relations, addition, multiplication, and restricted quantifiers.

Three substantial steps remain:

1. General machine realisation of primitive-recursive composition and recursion.
2. An internal halting formula with a satisfaction-adequacy theorem and effective formula coding.
3. A recursive syntax and effective translation for arbitrary arithmetic
   sentences, followed by the non-arithmeticality argument.

The arithmetic route can advance independently of a universal machine. Its
current formula fragment is not yet an effective translation of all arithmetic.
The finite-witness theorem still uses the external `finite_run` definition.
It does not discharge the internal-formula assumption. Neither a universal
machine nor the EPQ's full final theorem is claimed here.

## Read and run

- **Start with the model:** [Turing_Machine.thy](Turing_Machines_ZF/Turing_Machine.thy).
- **Follow a concrete calculation:** [copying](Turing_Machines_ZF/Turing_Copy.thy), then [addition and doubling](Turing_Machines_ZF/Turing_Arithmetic.thy).
- **Inspect the newest proofs:** [workspace preservation](Turing_Machines_ZF/Turing_Workspace.thy) and [model witnesses](Turing_Models/Turing_Model_Witnesses.thy).
- **Go deeper:** [development guide](documentation/DEVELOPMENT.md), [research review](papers/REVIEW_AND_ROADMAP.md), and [internalisation specification](papers/TURING_INTERNALISATION.md).

With [Isabelle2025-2](https://isabelle.in.tum.de/website-Isabelle2025-2/) installed:

```sh
isabelle build -D Turing_Machines_ZF
```

For the model-theoretic sessions, add the AFP snapshot dated **6 February 2026**:

```sh
isabelle components -u /absolute/path/to/afp-2026-02-06/thys
isabelle build -D .
```

See [reproduction instructions](documentation/BUILD.md) for download checksums,
session names, and the commands used in CI.

## Authorship and references

Tang Ziyi set the research question and developed the EPQ argument and initial
formalisation. Subsequent proof engineering and documentation include substantial
AI assistance; [the disclosure](AI_USAGE.md) distinguishes this work from direct
human authorship and review. The project has not received independent expert
peer review.

The machine's five-action normal form follows the design of AFP's
[Universal Turing Machine](https://www.isa-afp.org/entries/Universal_Turing_Machine.html),
which is formalised in Isabelle/HOL. This repository proves its results in ZF;
it does not inherit that entry's universality proof. The model-theoretic layer
uses [Independence of the Continuum Hypothesis](https://www.isa-afp.org/entries/Independence_CH.html)
and its dependencies.

Sources and documentation: [BSD 3-Clause](LICENSE). The EPQ paper is copyright
© 2026 Tang Ziyi; all rights reserved.
