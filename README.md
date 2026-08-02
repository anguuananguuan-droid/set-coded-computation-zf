# Set-Coded Computation in Isabelle/ZF

Tang Ziyi, Version 0.3, August 2026

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
| I.2 | [`Turing_Coding.thy`](Turing_Machines_ZF/Turing_Coding.thy) | Set-theoretic machine numbering | Implemented; effectivity remains open |
| II | [`Turing_CH.thy`](Turing_CH/Turing_CH.thy) | Conditional invariance equivalence | Implemented as a locale theorem |
| III | [Technical note](papers/TURING_INTERNALISATION.md) | Internal halting formula and adequacy | Specified, not implemented |

The checked source dependencies are

```text
ZF
└── Turing_Machines_ZF.Turing_Machine
    └── Turing_Machines_ZF.Turing_Coding ──┐
                                           ├── Turing_CH.Turing_CH
Independence_CH.Definitions_Main ──────────┘
```

The two remaining foundational paths are

```text
operational semantics
├── effective numeric operations -> universal simulation -> halting undecidability
└── finite-run formula -> satisfaction adequacy

both paths -> effective invariance reduction
```

Module II is proved conditionally inside `halting_sentence`. Module III will
construct the internal formula and adequacy theorem required to interpret that
locale. The coding path now provides a set-theoretic numbering. It must still
establish effective numeric operations, universal simulation, and the
undecidability theorem required by the final reduction.

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

Thus the development now has an explicit natural-number numbering and a total
decoder. This is a set-theoretic codec: the current proofs do not yet show that
its numeric operations belong to Isabelle/ZF's object-level `prim_rec` class.
The repository also does not yet contain a universal evaluator or a proof of
halting undecidability.

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
theorem. An effective reduction additionally requires effective machine and
formula encodings and a formal proof of halting undecidability.

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

The first machine-specific gate is the adequacy of a first-order formula for
one execution step. Finite-run or reachability adequacy, the internal halting
formula, machine-code quotation, and the concrete locale interpretation follow
from that gate.

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
