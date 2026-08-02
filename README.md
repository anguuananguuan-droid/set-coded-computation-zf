# Set-Coded Computation in Isabelle/ZF

Tang Ziyi, Version 0.7, August 2026

This repository contains a set-coded operational semantics for deterministic
binary Turing machines in Isabelle/ZF and a conditional application to
invariance across transitive set models of ZFC.

Substantive use of generative AI during development is documented in the
[AI assistance disclosure](AI_USAGE.md).

The project continues an integration programme exemplified by Lawrence C.
Paulson's [formalisation of Wetzel's problem](https://arxiv.org/abs/2205.03159).
Wetzel brings complex analysis and ZF set theory into one Isabelle development.
This project isolates an interface intended to connect external machine
execution with internal first-order satisfaction; constructing and discharging
that interface is the unfinished Module III. The analogy is deliberately
asymmetric: CH does not determine whether a machine halts. It supplies one
instance of the closed non-invariant sentence used by the general theorem.

## Status and architecture

| Module | Source | Result | Status |
| --- | --- | --- | --- |
| I.1 | [`Turing_Machine.thy`](Turing_Machines_ZF/Turing_Machine.thy) | Set-coded operational semantics | Implemented |
| I.2 | [`Turing_Coding.thy`](Turing_Machines_ZF/Turing_Coding.thy) | Set-theoretic machine numbering | Implemented |
| I.3 | [`Turing_Primrec.thy`](Turing_Machines_ZF/Turing_Primrec.thy) | Primitive-recursive arithmetic, pairing, and coded lists | Implemented |
| I.4 | [`Turing_Evaluator.thy`](Turing_Machines_ZF/Turing_Evaluator.thy) | Numeric evaluator and semantic simulation | Implemented |
| I.5 | [`Turing_Evaluator_Primrec.thy`](Turing_Machines_ZF/Turing_Evaluator_Primrec.thy) | Primitive-recursive evaluator certificates | Implemented through bounded blank-input halting |
| I.6 | [`Turing_Decidability.thy`](Turing_Machines_ZF/Turing_Decidability.thy) | Decision semantics and diagonal languages | Implemented |
| I.7 | [`Turing_Transformations.thy`](Turing_Machines_ZF/Turing_Transformations.thy) | Rejection transform, self-halting undecidability, and semantic input hardwiring | Implemented |
| I.8 | [`Turing_Transformations_Primrec.thy`](Turing_Machines_ZF/Turing_Transformations_Primrec.thy) | Primitive-recursive natural-code hardwiring | Implemented |
| II | [`Turing_CH.thy`](Turing_CH/Turing_CH.thy) | Conditional invariance equivalence | Implemented as a locale theorem |
| III | [Technical note](papers/TURING_INTERNALISATION.md) | Internal halting formula and adequacy | Specified, not implemented |

The checked source dependencies are

```text
ZF-Induct.Primrec ────────────────────────┐
                                         │
ZF ── Turing_Machine ── Turing_Coding    │
                              ├── Turing_Primrec ◄──┘
                              │       └── Turing_Evaluator
                              │               └── Turing_Evaluator_Primrec ──┐
                              │
                              ├── Turing_Decidability
                              │       └── Turing_Transformations ─────────────┤
                              │                                              └── Turing_Transformations_Primrec
                              │
                              └──────────────┐
Independence_CH.Definitions_Main ────────────┴── Turing_CH
```

The principal dependency paths are

```text
self-input halting undecidability
  -> semantic input hardwiring
  -> primitive-recursive self-hardwiring map
  -> Turing-machine realisation or decidable-preimage closure
  -> blank-input halting undecidability

machine numbering -> primitive-recursive numeric evaluator
  -> Turing-machine realisation and universal simulation

primitive-recursive bounded halting
  -> internal first-order formula -> satisfaction adequacy

blank-input undecidability + satisfaction adequacy + formula-code mapping
  -> effective invariance reduction
```

Module II is proved conditionally inside `halting_sentence`. Module III will
construct the internal formula and adequacy theorem required to interpret that
locale. Module I now proves that its self-input halting set is not decidable by
any machine in the formalised model and supplies both a verified machine-level
hardwiring transformation and a primitive-recursive transformation of natural
machine codes. Concluding blank-input halting undecidability still requires a
machine realisation theorem for primitive-recursive maps or a closure theorem
for `tm_decidable` under primitive-recursive preimages. The final invariance
reduction additionally requires formula-code effectivity and Module III
adequacy. Universal simulation remains a separate reusable infrastructure
target.

## Verified results

### Operational semantics

`Turing_Machine.thy` represents symbols, actions, tapes, instructions,
machines, configurations, and finite computations as ZF sets. The binary
five-action model follows the operational design of the AFP entry
[`Universal_Turing_Machine`](https://www.isa-afp.org/entries/Universal_Turing_Machine.html).

```text
(scan, update, slot, fetch)
              ↓
             step
              ↓
             steps
              ↓
          finite_run
              ↓
           halts_on
```

States `1` and `0` are initial and final. A tape is a pair of finite lists, an
empty boundary is read as blank, and missing instructions return
`<nop,final_state>`. The semantic operations are total.

`finite_run_iff_steps` identifies every finite run with the canonical sequence
of iterated steps. `halts_on_iff_finite_run` characterises halting by a finite
run from the initial configuration to a configuration with state `0`.

### Machine coding

`Turing_Coding.thy` constructs the machine-numbering layer in three stages.
`pair_code` and `pair_decode` form a bijection between `nat × nat` and `nat`.
`nat_list_encode` and `nat_list_decode` form a bijection between `list(nat)`
and `nat`. Each instruction is represented by one pair code, and a machine is
represented by the natural-number code of its instruction-code list.

Invalid action fields are totalised to `<nop,final_state>`. The set
`machine_code` contains exactly the canonical codes, while `decode_machine`
maps every natural number to a well-formed machine. The principal results are

```text
machine_numbering_bij:
  machine <-> machine_code

decode_machine_surj:
  nat ->> machine
```

Thus the development has an explicit natural-number numbering and a total
decoder. The following three theories establish a primitive-recursive numeric
evaluator over this numbering.

### Primitive-recursive numeric evaluation

`Turing_Primrec.thy` constructs object-level `prim_rec` witnesses for the
arithmetic, Cantor projections, and coded-list operations used by evaluation.
`Turing_Evaluator.thy` then defines natural-number codes for tapes and
configurations and implements numeric scanning, update, instruction fetch,
one-step execution, and finite iteration.

The central commuting theorem is

```text
e in nat and c in configuration ==>
  code_step(e,encode_configuration(c))
    = encode_configuration(step(decode_machine(e),c)).
```

It holds for every natural number `e`, including non-canonical instruction
streams, because instruction decoding and numeric instruction normalisation
use the same default instruction. Induction lifts the result from one step to
every finite number of steps.

`Turing_Evaluator_Primrec.thy` supplies explicit witnesses in Isabelle/ZF's
object-level `prim_rec` class for this complete numeric data flow. In
particular, it proves certificates for `code_step`, `code_steps`, and the
bounded blank-input halting predicate. The semantic endpoint is

```text
e in nat ==>
  (halts_blank(decode_machine(e))
    <-> (exists n in nat. code_halts_blank_at(n,e) = 1)).
```

This proves that the bounded computation predicate is primitive recursive. It
does not yet provide a Turing machine implementing the evaluator or a
universal Turing machine. Unbounded self-input halting is treated separately
by a direct machine-level diagonal argument.

### Decision semantics and diagonalisation

`Turing_Decidability.thy` defines unary numeral inputs, final-tape output,
decision semantics, and the self-input halting set

```text
self_halting =
  {e in nat. halts_on(decode_machine(e),numeral_input(e))}.
```

The machine numbering first yields the unconditional Cantor-style result

```text
not tm_decidable(diagonal_rejection).
```

`Turing_Transformations.thy` then supplies the operational content needed for
self-halting. Given a machine `M`, `rejecting_machine(M)` is a finite machine
that redirects every explicit transition to the final state, fills every
missing instruction slot that would otherwise halt by totalisation, and tests
the resulting output at a fresh bounded control state. It halts exactly when
`M` rejects:

```text
halts_on(rejecting_machine(M),numeral_input(n))
  <-> rejects_number(M,n).
```

The proof establishes a state bound, one-step and finite-step semantic
projection, and the invariant that every actual final configuration of the
transformed machine scans blank. Interpreting the abstract diagonal locale
with this concrete transform gives

```text
not tm_decidable(self_halting).
```

This is an unconditional undecidability theorem for self-input halting. A
universal machine remains open.

The same theory constructs `hardwire(M,x)` by compiling a finite loader,
shifting every non-final state of `M`, and appending the shifted instruction
table. The proof first establishes exact execution of the compiled loader,
then proves one-step and finite-step simulation of the shifted machine. Its
semantic endpoint is

```text
M in machine and x in list(symbol) ==>
  (halts_blank(hardwire(M,x)) <-> halts_on(M,x)).
```

Thus arbitrary-input halting has been reduced to blank-input halting at the
level of concrete set-coded machines.

`Turing_Transformations_Primrec.thy` implements the corresponding operation on
natural machine numbers. It normalises and shifts decoded instructions,
constructs the unary-input loader prefix, and proves

```text
hardwire_code(e,n)
  = encode_machine(hardwire(decode_machine(e),numeral_input(n))).
```

Every component has an explicit witness in Isabelle/ZF's object-level
`prim_rec` class. Diagonalising the second argument gives

```text
e in self_halting
  <-> self_hardwire_code(e) in blank_halting.
```

The primitive-recursive map and this pointwise equivalence are complete. The
development does not yet realise the map by a set-coded Turing machine or
prove that `tm_decidable` is closed under its preimages. Blank-input halting
undecidability is therefore not yet claimed.

### Invariance interface

`Turing_CH.thy` defines `zfc_invariant(phi)` as agreement of a closed formula
across all transitive set models of ZFC. Assuming a countable transitive model
of ZFC, `CH_not_invariant` obtains models satisfying CH and its negation from
the AFP entry `Independence_CH`.

The locale `halting_sentence` uses the verified total machine decoder from
`Turing_Coding.thy`. It assumes a closed formula `halt_fm(e)` and agreement
between satisfaction of that formula and blank-input halting. For `e in nat`
and every closed non-invariant sentence `sigma`, it proves

```text
e in nat
  ==>
  (zfc_invariant(Or(halt_fm(e), sigma))
    <-> halts_blank(decode_machine(e))).
```

Taking `sigma` to be CH gives the current CH instance. This is a semantic
equivalence under the named locale assumptions, not yet an undecidability
theorem. The machine layer now proves self-input halting undecidable and the
natural-code self-hardwiring map primitive recursive. Reaching the present
blank-input interface still requires a Turing-machine realisation theorem or a
corresponding preimage-closure theorem. An effective invariance reduction also
requires effective closed-formula encoding and the adequacy theorem of Module
III.

The accompanying [EPQ paper](papers/EPQ.pdf) gives the set-theoretic motivation
for this application.

## Missing interface: Module III

Module III will define the `halt_fm` parameter of `halting_sentence` and prove
its adequacy assumption as a theorem. Its final contract is

```text
e in nat and transitive_zfc_model(A)
  ==>
((A, [] satisfies halt_fm(e))
  <-> halts_blank(decode_machine(e))).
```

The completed numeric layer supplies a smaller candidate gate: construct a
first-order formula representing `code_halts_blank_at(n,e)` and prove that its
satisfaction agrees with the verified primitive-recursive predicate. Merely
proving membership in `prim_rec` does not construct this formula or establish
model absoluteness. The direct set-coded route through a first-order formula
for one execution step remains available as an alternative.

The [technical note](papers/TURING_INTERNALISATION.md) records the theorem
contracts, relevant `Transitive_Models` infrastructure, two candidate
constructions, and the implementation order.

## Build

Module I targets
[Isabelle2025-2](https://isabelle.in.tum.de/installation.html).

```bash
isabelle build -D Turing_Machines_ZF
```

Module II also requires the AFP release for Isabelle2025-2. This repository
was built against the AFP snapshot dated 2026-02-06.

```bash
isabelle components -u /absolute/path/to/afp-2026-02-06
isabelle build -D .
```

## License

Except for the EPQ paper, the Isabelle sources and repository documentation are
released under the [BSD 3-Clause License](LICENSE). The EPQ paper is copyright
© 2026 Tang Ziyi; all rights are reserved.
