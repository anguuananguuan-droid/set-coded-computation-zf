# Set-Coded Turing Machines in Isabelle/ZF

[![Build](https://github.com/anguuananguuan-droid/set-coded-computation-zf/actions/workflows/isabelle.yml/badge.svg?branch=main)](https://github.com/anguuananguuan-droid/set-coded-computation-zf/actions/workflows/isabelle.yml)

This library formalises deterministic Turing machines in Isabelle/ZF.
It provides execution semantics, natural-number encodings, and closed
set-theoretic formulas expressing machine halting. The satisfaction proofs
connect concrete computations with the existing Isabelle/ZF model libraries.

[Library guide](documentation/COMPUTATION.md) ·
[Proof document](papers/library/Set_Coded_Turing_Machines.pdf) ·
[Research summary](papers/Research_Summary.pdf)

## 1 Machine model

A machine is a finite instruction list over a binary alphabet. Its tape is
represented by two finite lists, with blank cells beyond their stored ends.
The semantics defines one step, finite execution, and halting. Observational
tape equality identifies representations differing only by stored blank
cells and preserves execution and halting.

The operational definitions are in
[Turing_Machine](thys/Set_Coded_Turing_Machines/Turing_Machine.thy).
[Turing_Tape](thys/Set_Coded_Turing_Machines/Turing_Tape.thy) gives the
representation equivalences, and
[Turing_Coding](thys/Set_Coded_Turing_Machines/Turing_Coding.thy) gives the
machine encoding and decoding theorems.

## 2 Halting inside a model

For each well-formed machine P and finite symbol input x, the library
constructs a closed first-order formula `halt_sentence(P,x)`. For every
transitive ZF set model M, it proves

```text
M satisfies halt_sentence(P,x)  if and only if  P halts on x.
```

The same sentence is used in every model. Its syntax, closedness, and
[satisfaction theorem](thys/Set_Coded_Turing_Machines/Turing_Halting_Sentences.thy#L192)
are proved from the machine, input, and model premises.

A [primitive-recursive constructor](thys/Set_Coded_Turing_Machines/Turing_Halting_Codes.thy#L34)
returns the exact sentence code from a natural machine code and unary input.
This certifies numerical syntax construction. The semantic theorem itself
accepts any finite symbol input.

## 3 Use

The public session is `Set_Coded_Turing_Machines`. Select the interface
needed by a client, for example

```text
theory My_Machine
  imports "Set_Coded_Turing_Machines.Turing_Machine"
begin

end
```

The [library guide](documentation/COMPUTATION.md) gives the client ROOT,
machine conventions, and proof interfaces.
[Turing_Examples](thys/Set_Coded_Turing_Machines/Turing_Examples.thy)
proves a two-instruction program correct.
[Turing_Halting_Examples](thys/Set_Coded_Turing_Machines/Turing_Halting_Examples.thy)
uses that result through the satisfaction and sentence-code interfaces.

## 4 Build

The verified environment is
[Isabelle2025-2](https://isabelle.in.tum.de/website-Isabelle2025-2/) with
[AFP 2026-10-06](https://isa-afp.org/release/afp-2026-10-06.tar.gz).
With Isabelle on the executable search path, run from this directory

```text
isabelle components -u /absolute/path/to/afp-2026-10-06/thys
isabelle build -d . Set_Coded_Turing_Machines
```

The complete session uses the model interfaces supplied by
`Independence_CH`. The halting theorem has no CH independence or choice
premise. [Build instructions](documentation/BUILD.txt) also cover the
independent ZF computation fragment, archive export, and verification.
Compatibility with Isabelle2026 has not yet been checked.

## 5 Documents and development

| Material | Contents |
| --- | --- |
| [Research summary](papers/Research_Summary.pdf) | One-page introduction to the question and verified result |
| [Proof outline](papers/library/Set_Coded_Turing_Machines_Outline.pdf) | Definitions, theorem statements, explanations, and references |
| [Complete proofs](papers/library/Set_Coded_Turing_Machines.pdf) | Generated Isabelle document including the proofs |
| [EPQ paper](papers/EPQ.pdf) | Repository copy of the paper that motivated the formalisation |
| [EPQ production log](papers/EPQ_Log.pdf) | The completed candidate sections, starting with the research narrative |

The [papers index](papers/README.md) identifies document versions and
provides the complete log form and Word copy.

The [library](thys/Set_Coded_Turing_Machines) contains seventeen theories
and is the standalone AFP candidate. [Research extensions](documentation/RESEARCH.md)
cover the separate computation and model-invariance applications. Their
open objectives include the full EPQ formalisation. The library has not
been submitted to AFP.

## 6 Sources and maintenance

The machine design follows
[Universal Turing Machine](https://isa-afp.org/entries/Universal_Turing_Machine.html).
Model closure and satisfaction use
[Transitive Models](https://isa-afp.org/entries/Transitive_Models.html)
and the interpretations in
[Independence_CH](https://isa-afp.org/entries/Independence_CH.html).

Maintained by Tang Ziyi under the [BSD 3-Clause License](LICENSE).
[Citation](CITATION.cff) · [Documentation](documentation/README.md) ·
[Verification record](documentation/records/RV.012.txt) ·
[Contributing](CONTRIBUTING.txt) ·
[Issues](https://github.com/anguuananguuan-droid/set-coded-computation-zf/issues)
