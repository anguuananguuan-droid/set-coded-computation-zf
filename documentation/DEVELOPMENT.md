# Formal development guide

Detailed guide to the development. Updated 4 October 2026.

For current results and build instructions, start with the [repository homepage](../README.md).

This repository contains a set-coded operational semantics for deterministic
binary Turing machines in Isabelle/ZF and a conditional application to
invariance across transitive set models of ZFC.

The independently buildable `Set_Coded_Computation_ZF` session contains eight
theories under `Turing_Machines_ZF/Core`. The original
`Turing_Machines_ZF` session extends it with program and primitive-recursive
work; `Turing_CH` and `Turing_Models` remain separate applications.

Substantive use of generative AI during development is documented in the
[AI assistance disclosure](../AI_USAGE.md).

The project continues an integration programme exemplified by Lawrence C.
Paulson's [formalisation of Wetzel's problem](https://arxiv.org/abs/2205.03159).
Wetzel integrates complex analysis with the ZFC library inside Isabelle/HOL;
this repository instead works in Isabelle/ZF.
This project isolates an interface intended to connect external machine
execution with internal first-order satisfaction; constructing and discharging
that interface is the unfinished Module III. The analogy is deliberately
asymmetric: CH does not determine whether a machine halts. It supplies one
instance of the closed non-invariant sentence used by the general theorem.

The [research review and roadmap](../papers/REVIEW_AND_ROADMAP.md) records a
numerical-output defect found in the previous version and its correction.
Output is now compared by represented tape contents, ignoring trailing blanks.
The roadmap also distinguishes the halting application from the stronger
non-arithmetical index-set conclusion of the EPQ.

## Status and architecture

| Module | Source | Result | Status |
| --- | --- | --- | --- |
| I.1 | [`Turing_Machine.thy`](../Turing_Machines_ZF/Core/Turing_Machine.thy) | Set-coded operational semantics | Implemented |
| I.1a | [`Turing_Tape.thy`](../Turing_Machines_ZF/Core/Turing_Tape.thy) | Tape-content equivalence and finite-step congruence | Implemented |
| I.2 | [`Turing_Coding.thy`](../Turing_Machines_ZF/Core/Turing_Coding.thy) | Set-theoretic machine numbering | Implemented |
| I.2a | [`Turing_Code_Operations.thy`](../Turing_Machines_ZF/Core/Turing_Code_Operations.thy) | Pure operations on pair and list codes, separated from PR certificates | Implemented |
| I.3 | [`Turing_Primrec.thy`](../Turing_Machines_ZF/Turing_Primrec.thy) | Primitive-recursive arithmetic, pairing, and coded lists | Implemented |
| I.4 | [`Turing_Evaluator.thy`](../Turing_Machines_ZF/Core/Turing_Evaluator.thy) | Numeric evaluator and semantic simulation | Implemented |
| I.5 | [`Turing_Evaluator_Primrec.thy`](../Turing_Machines_ZF/Turing_Evaluator_Primrec.thy) | Primitive-recursive evaluator certificates | Implemented through bounded blank-input halting |
| I.6 | [`Turing_Decidability.thy`](../Turing_Machines_ZF/Core/Turing_Decidability.thy) | Decision semantics and diagonal languages | Implemented |
| I.7 | [`Turing_Transformations.thy`](../Turing_Machines_ZF/Turing_Transformations.thy) | Input loading, state shifting, and semantic input hardwiring | Implemented in the extended session |
| I.7a | [`Turing_Rejection.thy`](../Turing_Machines_ZF/Core/Turing_Rejection.thy) | Concrete rejection transform and unconditional self-halting undecidability | Independent core session |
| I.8 | [`Turing_Transformations_Primrec.thy`](../Turing_Machines_ZF/Turing_Transformations_Primrec.thy) | Primitive-recursive natural-code hardwiring | Implemented |
| I.9 | [`Turing_Composition.thy`](../Turing_Machines_ZF/Turing_Composition.thy) | Sequential machine composition and bidirectional termination semantics | Implemented |
| I.10 | [`Turing_Reduction.thy`](../Turing_Machines_ZF/Turing_Reduction.thy) | Canonical numerical computation and machine many-one reductions | Implemented |
| I.10a | [`Turing_Basic.thy`](../Turing_Machines_ZF/Turing_Basic.thy) | Concrete identity, successor, and zero machines | Implemented |
| I.10b | [`Turing_Programs.thy`](../Turing_Machines_ZF/Turing_Programs.thy) and [`Turing_Arguments.thy`](../Turing_Machines_ZF/Turing_Arguments.thy) | Composable tape transformations and unambiguous argument lists | Implemented |
| I.10c | [`Turing_Copy.thy`](../Turing_Machines_ZF/Turing_Copy.thy) and [`Turing_Arithmetic.thy`](../Turing_Machines_ZF/Turing_Arithmetic.thy) | Binary copying, addition, and a machine realising `pr_double` | Implemented |
| I.10d | [`Turing_Storage.thy`](../Turing_Machines_ZF/Turing_Storage.thy) and [`Turing_Projection.thy`](../Turing_Machines_ZF/Turing_Projection.thy) | Argument erasure, all projections, and list-based successor | Implemented, including empty and short argument lists |
| I.10e | [`Turing_Realisation.thy`](../Turing_Machines_ZF/Turing_Realisation.thy) and [`Turing_Context.thy`](../Turing_Machines_ZF/Turing_Context.thy) | All constant functions, unary-interface bridge, and workspace counterexample | Basis implemented; general `COMP` and `PREC` closure open |
| I.10f | [Turing_Workspace.thy](../Turing_Machines_ZF/Core/Turing_Workspace.thy) | Exact preservation of arbitrary saved tape data through bounded executions | Implemented; the time bound is supplied |
| I.11 | [`Turing_Primrec_Reduction.thy`](../Turing_Machines_ZF/Turing_Primrec_Reduction.thy) | Primitive-recursive reductions and their machine-realisation interface | Implemented; the required realiser remains open |
| II | [`Turing_CH.thy`](../Turing_CH/Turing_CH.thy) | Uniform-truth disjunction principle and conditional halting/nonhalting equivalences | General principle proved; halting instances remain conditional |
| III.1 | [Turing_Model_Witnesses.thy](../Turing_Models/Turing_Model_Witnesses.thy) | Machines, configurations, and finite halting certificates belong to every transitive ZFC model | Closure and external witness equivalence proved |
| III.1a | [Turing_Arithmetic_Truth.thy](../Turing_Models/Turing_Arithmetic_Truth.thy) | Standard naturals, zero, successor, order, addition, multiplication, and restricted quantifiers agree with model satisfaction | Verified first-order fragment; full syntax translation open |
| III.2 | [Technical note](../papers/TURING_INTERNALISATION.md) | Internal halting formula and adequacy | Specified, not implemented |

The checked source dependencies are

```text
ZF -> Turing_Machine -> Turing_Coding -> Turing_Code_Operations -> Turing_Evaluator
                   -> Turing_Tape -> Turing_Workspace
Turing_Coding -> Turing_Decidability -> Turing_Rejection

Turing_Code_Operations + ZF-Induct.Primrec
  -> Turing_Primrec
Turing_Evaluator + Turing_Primrec -> Turing_Evaluator_Primrec

Turing_Rejection -> Turing_Transformations -> Turing_Composition
Turing_Composition + Turing_Tape -> Turing_Reduction
Turing_Reduction + ZF-Induct.Primrec -> Turing_Basic
Turing_Basic -> Turing_Programs -> Turing_Arguments
Turing_Arguments -> Turing_Storage -> Turing_Projection
Turing_Arguments -> Turing_Copy
Turing_Copy + Turing_Primrec -> Turing_Arithmetic
Turing_Projection + Turing_Arithmetic -> Turing_Realisation -> Turing_Context -> Turing_Workspace

Turing_Transformations + Turing_Evaluator_Primrec
  -> Turing_Transformations_Primrec

Turing_Reduction + Turing_Transformations_Primrec
  -> Turing_Primrec_Reduction

Turing_Coding + Independence_CH.Definitions_Main
  -> Turing_CH -> Turing_Model_Witnesses -> Turing_Arithmetic_Truth
```

The principal dependency paths are

```text
self-input halting undecidability
  -> semantic input hardwiring
  -> primitive-recursive self-hardwiring map
  -> primitive-recursive many-one reduction
  -> Turing-machine realisation of the reducing map
  -> machine many-one reduction and decidability closure
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
locale. Module I proves that its self-input halting set is not decidable by any
machine in the formalised model. It supplies semantic and natural-code
hardwiring, sequential machine composition, machine many-one reductions, and
closure of `tm_decidable` under those reductions. The self-hardwiring function
is primitive recursive and reduces self-input halting to blank-input halting.
Concluding blank-input halting undecidability now has one isolated operational
obligation: construct a set-coded machine that computes this primitive-recursive
function. The final invariance reduction additionally requires formula-code
effectivity and Module III adequacy. Universal simulation remains a separate
reusable infrastructure target.

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
development does not yet realise the map by a set-coded Turing machine.

### Sequential composition and many-one reduction

`Turing_Composition.thy` constructs `sequential_machine(M,N)`. Its continuation
table redirects every explicit transition of `M` whose target is state `0`,
and every missing instruction that would halt by totalisation, into a handoff
to a shifted copy of `N`. The construction therefore covers both ways in which
the operational semantics can halt. The principal semantic theorem has the
assumptions

```text
M in machine
N in machine
c in configuration
fst(c) in control_bound(M)
fst(c) != final_state
```

and concludes

```text
sequential_machine(M,N) terminates from c
  <-> M terminates from c and N terminates from the tape left by M.
```

The proof establishes exact simulation before the handoff, exact shifted
simulation afterwards, and the converse decomposition of every terminating
composed run.

`Turing_Tape.thy` compares half-tapes at every natural position, treating
unrepresented positions as blank. It proves that scanning, updates, and every
finite computation respect tape-content equivalence. `Turing_Reduction.thy`
defines `computes_number(M,n,m)` by equivalence of the final configuration to
the unary numeral for `m`, including the final state and head alignment.
The output is unique. Literal list equality would forbid every output smaller
than its input; `literal_numeral_output_not_smaller` proves this obstruction.
`Turing_Basic.thy` supplies concrete identity, successor, and zero machines,
including `zero_computes` for every natural input.
`computes_number_sequential` composes numerical computations;
`zero_then_successor_computes_one` checks its use on the blank-padded tape
left by erasure.

Sequential composition passes the actual output tape and gives

```text
computes_number(R,n,m) ==>
  D in machine ==>
  (yields(sequential_machine(R,D),numeral_input(n),b)
    <-> yields(D,numeral_input(m),b)).
```

This result lifts to accept and reject semantics and proves closure of
`tm_decidable` under the machine many-one relation `tm_many_one_reducible`.

`Turing_Primrec_Reduction.thy` separates an extensional primitive-recursive
reduction from its operational realisation. It proves unconditionally that
`pr_self_hardwire_code` reduces `self_halting` to `blank_halting`, and proves

```text
tm_realises_unary(R,pr_self_hardwire_code) ==>
  not tm_decidable(blank_halting).
```

Thus the preimage-closure argument is complete. Blank-input halting
undecidability is not yet unconditional because the machine `R` has not yet
been constructed.

### Concrete programs and the primitive-recursive basis

`arguments(ns)` represents each natural argument `n` by `n+1` strokes and a
blank separator. `arguments_eq_imp_equal` proves that even after ignoring
trailing blanks, different argument lists remain distinguishable. The original
unary input convention remains `n` strokes. `successor_arguments_computes`
connects it to a singleton argument list by an actual finite machine.

The eight-state binary `copy_machine` duplicates a unary block. Composing it
with the input adapter gives `duplicate_arguments_computes`, producing the
argument list `[n,n]` for every natural `n`. The nine-state `addition_machine`
consumes `[n,m]`, clears the representation overhead, and produces `n+m`.
Their composition establishes

```text
n in nat ==> computes_number(doubling_machine,n,n #+ n)
tm_realises_unary(doubling_machine,pr_double).
```

Storage programs delete the first argument, erase an arbitrary argument list,
and retain the first argument while clearing the rest and restoring the head.
`tm_realises_arguments(M,f)` requires correct numerical output on **every**
list of natural arguments. Concrete machine witnesses now establish

```text
tm_realises_arguments(keep_first_machine,SC)
i in nat ==> tm_realises_arguments(projection_machine(i),PROJ(i))
k in nat ==> tm_realises_arguments(constant_arguments_machine(k),CONSTANT(k)).
```

These contracts include the library's empty-list cases and out-of-range
projections. `argument_realiser_to_unary` translates this interface into
`tm_realises_unary` using a concrete input adapter.

This completes the primitive-recursive **basis**, not the general realisation
theorem. Arbitrary `COMP` and `PREC` need protected storage for retained
arguments and intermediate results. `Turing_Context.thy` proves a concrete
counterexample: a machine can compute numerical identity on a blank context
while erasing a saved stroke to its left. Standalone numerical correctness
therefore supplies no automatic workspace-preservation rule. The general
compiler must establish that additional discipline or implement a simulator
that protects the stored data. The self-hardwiring and universal-evaluator
realisers remain open.

### Bounded workspaces and model witnesses

`Turing_Workspace.thy` appends saved tape lists outside a finite workspace.
`steps_preserve_frame` proves exact equality between a framed execution and
framing its result, whenever both tape halves initially have at least as many
cells as the supplied step count. `bounded_workspace_history` pads any
configuration with `n` blank cells per side and proves this property for
every `k <= n`, together with content equivalence to the original execution.
The theorem supplies bounded isolation; it neither predicts a halting time
nor compiles arbitrary subroutines into safe unbounded workspaces.

`Turing_Model_Witnesses.thy` proves finite-list and finite-function closure in
AFP's existing `M_trivial` locale, then derives that locale from the actual
`transitive_zfc_model` definition. Consequently every machine, configuration,
and canonical finite trace belongs to every transitive ZFC set model.
`transitive_zfc_halting_witness_iff` characterises external halting by the
existence of such a certificate inside the model. Its `finite_run` predicate
is still external: it is not yet a formula interpreted by `sats`.

`Turing_Arithmetic_Truth.thy` starts a separate route to the EPQ conclusion.
It proves satisfaction equivalences for the standard-natural-number domain,
zero, successor, order, addition, multiplication, and quantifiers explicitly
restricted to natural numbers in every transitive ZFC set model. These are
basic syntax and semantic lemmas; a recursive source syntax, an effective
translation for arbitrary arithmetic sentences, and the reduction itself
remain to be built. This route does not need
the unfinished universal-machine/compiler result as a premise.

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
natural-code self-hardwiring map primitive recursive. It also proves the
many-one preimage-closure theorem. Reaching the present blank-input interface
now requires the set-coded machine realising that map. An effective invariance
reduction additionally requires effective closed-formula encoding and the
adequacy theorem of Module III.

The complementary locale theorem
`nonhalting_or_invariant_iff_not_halts_blank` proves the corresponding
nonhalting equivalence using `Or(Neg(halt_fm(e)),sigma)`. Both are instances of
`uniform_or_invariant_iff`, which turns any uniformly true-or-false closed
sentence into an invariance test by disjoining a fixed non-invariant sentence.

The accompanying [EPQ paper](../papers/EPQ.pdf), Section V, has a stronger final
target: true arithmetic many-one reduces to the codes of invariant sentences,
so that index set is not arithmetical. Reaching it additionally requires
arithmetic syntax and truth, an effective translation into set-theoretic
formulas, arithmetic satisfaction adequacy, and the non-definability argument.
The halting and nonhalting reductions alone establish a weaker endpoint once
their effectivity and the enumerability infrastructure are supplied; they do
not prove non-arithmeticality. See the [review](../papers/REVIEW_AND_ROADMAP.md)
for the staged completion criteria.

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

The [technical note](../papers/TURING_INTERNALISATION.md) records the theorem
contracts, relevant `Transitive_Models` infrastructure, two candidate
constructions, and the implementation order.

## Build

See [reproduction instructions](BUILD.md) for all three sessions, fixed downloads,
and the public CI configuration.

Module I targets
[Isabelle2025-2](https://isabelle.in.tum.de/installation.html).

```bash
isabelle build -D Turing_Machines_ZF
```

Module II also requires the AFP release for Isabelle2025-2. This repository
was built against the AFP snapshot dated 2026-02-06.

```bash
isabelle components -u /absolute/path/to/afp-2026-02-06/thys
isabelle build -D .
```

## License

Except for the EPQ paper, the Isabelle sources and repository documentation are
released under the [BSD 3-Clause License](../LICENSE). The EPQ paper is copyright
© 2026 Tang Ziyi; all rights are reserved.
