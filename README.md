# Set-Coded Turing Machines in Isabelle/ZF

This library connects Turing-machine execution with truth inside models of
set theory. It defines machines and finite runs as sets, constructs closed
first-order sentences expressing halting, and proves that their meaning in
transitive ZF models agrees with external execution.

Read the [research summary](papers/Research_Summary.pdf),
[proof outline](papers/library/Set_Coded_Turing_Machines_Outline.pdf), or
[complete proof document](papers/library/Set_Coded_Turing_Machines.pdf).
The [library guide](documentation/COMPUTATION.md) gives the interfaces for
using the development in another Isabelle/ZF theory.

## 1 Result

For a well-formed machine P and finite symbol input x, `halt_sentence(P,x)`
is an explicit formula with no free variables. For every transitive ZF
set model M,

```text
M satisfies halt_sentence(P,x)  iff  P halts on x.
```

The sentence depends only on P and x. A program proof can therefore
establish its truth or falsity inside each model. The theorem assumes that
M is a transitive ZF set model and does not assert that such a model exists.
A weaker locale interface is also available.

The source proves [formula membership](thys/Set_Coded_Turing_Machines/Turing_Halting_Sentences.thy#L135),
[closedness](thys/Set_Coded_Turing_Machines/Turing_Halting_Sentences.thy#L146),
and the [satisfaction equivalence](thys/Set_Coded_Turing_Machines/Turing_Halting_Sentences.thy#L192).

For natural machine code e and unary input n, a primitive-recursive
constructor returns the code of
`halt_sentence(decode_machine(e),numeral_input(n))`. Its membership in
`prim_rec` and its equality to this exact formula code are proved. The
self-input case uses n = e. The
[primitive-recursion certificate](thys/Set_Coded_Turing_Machines/Turing_Halting_Codes.thy#L29)
and [exact code equation](thys/Set_Coded_Turing_Machines/Turing_Halting_Codes.thy#L34)
are separate proved statements. The certificate concerns numerical sentence
construction.

The proof rests on finite witnesses. A halting execution supplies a finite
trace belonging to the model. Conversely, induction recovers the external
execution from the internal witness's transition constraints. The proof
needs neither the entire external evaluator inside the model nor a
prescribed representation for every internal witness.

## 2 Use

The worked example scans a unary input, writes a stroke at the first blank,
and halts. Its operational proof supplies the following theorem inside every
transitive ZF set model. The client uses the public satisfaction interface.

```isabelle
theory Library_Use
  imports "Set_Coded_Turing_Machines.Turing_Examples"
    "Set_Coded_Turing_Machines.Turing_Halting_Sentences"
begin

theorem scan_append_in_model:
  assumes model: "transitive_zf_model(A)" and n: "n ∈ nat"
  shows "(A, [] ⊨ halt_sentence(scan_append_machine,numeral_input(n)))"
  using sats_halt_sentence_iff[OF model scan_append_machine_type
      numeral_input_type[OF n]] scan_append_halts[OF n] by simp

end
```

The [library guide](documentation/COMPUTATION.md) gives the client ROOT,
build command, machine conventions, and proof interfaces. Choose the import
needed by a client.

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
continues the same example through internal satisfaction and numerical
sentence codes. Its proofs use the interfaces without unfolding the
halting formula or the code constructor.

## 3 Build

The verified environment is
[Isabelle2025-2](https://isabelle.in.tum.de/website-Isabelle2025-2/)
with the [AFP snapshot of 6 October 2026](https://isa-afp.org/release/afp-2026-10-06.tar.gz).
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

## 4 Scope and sources

The library contains seventeen theories in one session. Applications to
invariant sentences, decision semantics, numeric evaluation, and larger
programs are maintained separately under `thys/Research`.
[Research extensions](documentation/RESEARCH.md) describes their results
and remaining obligations. The library is an AFP candidate and has not
been submitted or accepted.

| Location | Contents |
| --- | --- |
| [thys/Set_Coded_Turing_Machines](thys/Set_Coded_Turing_Machines) | The seventeen-theory candidate library |
| [thys/Research](thys/Research) | Separate applications and ongoing computation research |
| [papers](papers/README.md) | Research summary, generated proof documents, and the motivating EPQ |
| [documentation](documentation/README.md) | Library guide, reproduction instructions, and verification records |
| [scripts](scripts) | Archive export and source, client, proof, and document checks |

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
records. The [verification record](documentation/records/RV.011.txt)
identifies the proof-source revision, archive checksum, and the published
PDFs. The documents contain 108 pages of complete proofs and a 68-page
outline, built from the same sources.
[GitHub Actions](https://github.com/anguuananguuan-droid/set-coded-computation-zf/actions/workflows/isabelle.yml)
retains proof, client, style, archive, and document checks for each revision.
Report problems through [Issues](https://github.com/anguuananguuan-droid/set-coded-computation-zf/issues).
[Contributing](CONTRIBUTING.txt) describes the source and verification rules.
