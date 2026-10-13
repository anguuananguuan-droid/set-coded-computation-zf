# Set-Coded Turing Machines in Isabelle/ZF

Tang Ziyi

## 1 Library

A library of deterministic Turing machines represented as sets in
Isabelle/ZF. It provides finite execution, observational equality of tape
representations, and an explicit set-theoretic formula for halting.

For a machine P and a finite input x, `halt_sentence(P,x)` is a closed
formula. In every transitive ZF set model, it is true exactly when P halts
on x in the external execution semantics. The satisfaction proofs also
apply directly in the weaker `M_ZF1_trans` locale.

The library supplies natural-number codes for machines and formulas. A
primitive-recursive function constructs the code of each self-input
halting sentence. This certificate concerns sentence construction, not a
general compiler from primitive-recursive functions to this machine model.

## 2 Use

[The library guide](documentation/COMPUTATION.md) describes the machine
conventions, imports, proof interfaces, and build commands for a client.

- [Turing_Machine](thys/Set_Coded_Turing_Machines/Turing_Machine.thy)
  defines instructions, configurations, finite execution, and halting.
- [Turing_Tape](thys/Set_Coded_Turing_Machines/Turing_Tape.thy)
  relates finite lists that represent the same tape contents.
- [Turing_Examples](thys/Set_Coded_Turing_Machines/Turing_Examples.thy)
  proves a scanning program's result on every unary input, including a
  representation with an extra stored blank.
- [Turing_Halting_Sentences](thys/Set_Coded_Turing_Machines/Turing_Halting_Sentences.thy)
  connects machine halting to internal satisfaction.
- [Turing_Halting_Examples](thys/Set_Coded_Turing_Machines/Turing_Halting_Examples.thy)
  uses the program proof to establish truth inside a transitive model.
- [Turing_Halting_Codes](thys/Set_Coded_Turing_Machines/Turing_Halting_Codes.thy)
  certifies the numerical construction of self-input halting sentences.

## 3 Build and scope

The maintained session is
[Set_Coded_Turing_Machines](thys/Set_Coded_Turing_Machines/ROOT).
It contains seventeen theories, including the two worked examples.
[Build instructions](documentation/BUILD.txt) specify Isabelle2025-2,
AFP dependencies, archive export, and proof and document checks.

The machine, tape, examples, and numerical machine infrastructure can be
checked independently using only bundled Isabelle/ZF and ZF-Induct.

```sh
python3 scripts/check_computation.py --isabelle /absolute/path/to/isabelle --directory output/computation-check
```

The complete session uses model locales and interpretations supplied by
`Independence_CH`. The halting interface uses neither CH independence nor
choice. This source dependency is retained explicitly.

[Candidate scope](documentation/AFP.txt) states the formal contribution
and its boundaries. The entry has not been submitted or accepted.
[Research extensions](documentation/RESEARCH.md) retain the self-halting
undecidability proof, CH application, numeric evaluator, and larger program
constructions outside the candidate archive.

## 4 Sources and maintenance

The operational design follows the Isabelle/HOL AFP entry
[Universal Turing Machine](https://isa-afp.org/entries/Universal_Turing_Machine.html).
The objects and proofs here use Isabelle/ZF. Internal satisfaction uses
[Transitive Models of Fragments of ZFC](https://isa-afp.org/entries/Transitive_Models.html)
and model interpretations from
[Independence_CH](https://isa-afp.org/entries/Independence_CH.html).
The contribution is their verified connection to this machine semantics.
No new classical theorem or priority claim is made.

Tang Ziyi wrote the original EPQ paper, conceived the initial formalisation,
and constructed initial formal objects. The author has led and participated
throughout. Codex and ChatGPT assisted development. Aristotle and Anthropic
Claude participated in internal review and cross-checking. [AI assistance](AI_USAGE.txt)
records the activities and verification requirements.

The library and documentation use the [BSD 3 Clause License](LICENSE).
[Citation metadata](CITATION.cff), [contribution rules](CONTRIBUTING.txt),
and [engineering rules](AGENTS.md) describe maintenance.
[Development records](documentation/history/README.md) preserve earlier
scopes and verification evidence. [GitHub Actions](https://github.com/anguuananguuan-droid/set-coded-computation-zf/actions/workflows/isabelle.yml)
checks the source revision and retains the build artifacts.
