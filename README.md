# Set-Coded Turing Machines in Isabelle/ZF

A library of deterministic Turing machines represented as sets. It connects
finite execution, observational tape equality, and internal satisfaction
in transitive models of set theory.

## 1 Result

For a well-formed machine P and finite input x, `halt_sentence(P,x)` is an
explicit closed formula of set theory. In every transitive ZF set model M,

```text
M satisfies halt_sentence(P,x)  iff  P halts on x.
```

The library proves this equivalence from the machine semantics. A program
proof can therefore establish truth of its halting sentence inside a model.
The theorem is conditional on M being a transitive ZF set model and does
not assert that such a model exists. A weaker locale interface is also
available.

Natural-number codes for machines and formulas support a primitive-recursive
constructor with separate machine-code and unary-input arguments. Its output
is the code of the corresponding closed halting sentence. The self-input
constructor is a special case. This certifies sentence construction, not a
general compiler to the machine model.

## 2 Build

Use [Isabelle2025-2](https://isabelle.in.tum.de/website-Isabelle2025-2/)
and the [AFP snapshot of 6 October 2026](https://isa-afp.org/release/afp-2026-10-06.tar.gz).
With Isabelle on the executable search path, run from the repository root.

```sh
isabelle components -u /absolute/path/to/afp-2026-10-06/thys
isabelle build -d . Set_Coded_Turing_Machines
```

The session uses the model infrastructure in `Independence_CH`. Its halting
theorems use no CH independence result or choice assumption. The machine
and numerical machine fragment can also be checked separately with bundled
Isabelle/ZF and ZF-Induct. [Build instructions](documentation/BUILD.txt)
cover that check, all research sessions, archive export, and PDF generation.

## 3 Use

Import the interface needed by a client theory.

```isabelle
theory My_Machine
  imports "Set_Coded_Turing_Machines.Turing_Machine"
begin

end
```

The [library guide](documentation/COMPUTATION.md) gives the client ROOT,
build command, machine conventions, and proof interfaces.

| Theory | Interface |
| --- | --- |
| [Turing_Machine](thys/Set_Coded_Turing_Machines/Turing_Machine.thy) | Execution, finite witnesses, and rules for proving halting or nonhalting |
| [Turing_Tape](thys/Set_Coded_Turing_Machines/Turing_Tape.thy) | Observational equivalence preserving execution and halting |
| [Turing_Coding](thys/Set_Coded_Turing_Machines/Turing_Coding.thy) | Machine encoding, decoding, and canonical natural-number codes |
| [Turing_Halting_Sentences](thys/Set_Coded_Turing_Machines/Turing_Halting_Sentences.thy) | Closed halting sentences and their satisfaction theorem |
| [Turing_Halting_Codes](thys/Set_Coded_Turing_Machines/Turing_Halting_Codes.thy) | Primitive-recursive sentence codes and their satisfaction contract |

[Turing_Examples](thys/Set_Coded_Turing_Machines/Turing_Examples.thy)
proves a two-instruction scanning program correct on every unary input,
then transfers the result to a blank-padded tape.
[Turing_Halting_Examples](thys/Set_Coded_Turing_Machines/Turing_Halting_Examples.thy)
derives truth of its halting sentence from that program proof.

## 4 Scope and sources

The library contains seventeen theories in one session. Applications to
invariant sentences, decision semantics, numeric evaluation, and larger
programs are maintained separately under `thys/Research`.
[Research extensions](documentation/RESEARCH.md) describes their results
and remaining obligations. The library is an AFP candidate and has not
been submitted or accepted.

The machine design follows [Universal Turing Machine](https://isa-afp.org/entries/Universal_Turing_Machine.html).
Model closure and satisfaction use [Transitive Models of Fragments of ZFC](https://isa-afp.org/entries/Transitive_Models.html)
and the interpretations supplied by [Independence_CH](https://isa-afp.org/entries/Independence_CH.html).
The contribution is the verified connection between explicit machine
execution and these Isabelle/ZF model interfaces.

## 5 Maintenance

Maintained by Tang Ziyi under the [BSD 3-Clause License](LICENSE).
[Citation metadata](CITATION.cff) identifies the project. Cite the commit
used to make the version of a result explicit.

[Documentation](documentation/README.md) indexes the guides and project
records. The [verification record](documentation/records/RV.009.txt)
identifies the checked source revision, archive checksum, and build evidence.
[GitHub Actions](https://github.com/anguuananguuan-droid/set-coded-computation-zf/actions/workflows/isabelle.yml)
retains proof, client, style, archive, and document checks for each revision.
Report problems through [Issues](https://github.com/anguuananguuan-droid/set-coded-computation-zf/issues).
[Contributing](CONTRIBUTING.txt) describes the source and verification rules.
