# INTERNALISING TURING-MACHINE COMPUTATION IN ISABELLE/ZF

Tang Ziyi, Technical Design Note, August 2026; updated 4 October 2026

## 1. PURPOSE AND SEMANTIC BASIS

This note specifies Module III of the development. Its task is to replace the
semantic assumption `sats_halt_fm_iff` in `Turing_CH.thy` with a theorem.

The external meaning of computation is given by `step`, `steps`, `finite_run`,
and `halts_blank` in `Turing_Machine.thy`. The internal meaning is satisfaction
of a first-order set-theoretic formula inside a transitive set model of ZFC.

The verified operational basis is

```text
finite_run(P,n,r) and r(0) = c
  <->
r is the function k in succ(n) |-> steps(P,c,k),
```

together with the characterisation

```text
halts_on(P,x)
  <->
there exist n and r such that
  r is a finite run from initial_config(x)
  and r(n) has final state 0,
```

with the machine, input, and time typing conditions stated in the formal
theorem. The finite witness `r` is the object whose existence must be
recognised by a first-order formula.

The verified numeric basis now also provides

```text
e in nat implies
  (halts_blank(decode_machine(e))
    <->
  there exists n in nat such that code_halts_blank_at(n,e) = 1),

pr_code_halts_blank_at in prim_rec.
```

Thus blank-input halting already has the external shape of an existential
quantifier over a primitive-recursive bounded predicate. Membership in
`prim_rec` is not itself a first-order formula or an absoluteness theorem; the
remaining task is to represent this particular witness inside the model and
prove satisfaction adequacy.

Module III ends with a concrete interpretation of `halting_sentence`.
The machine layer now proves the self-input halting set undecidable. An
explicit machine-level hardwiring theorem now reduces arbitrary-input halting
to blank-input halting. The induced natural-code transformation now has an
explicit object-level `prim_rec` witness and a proved pointwise reduction from
self-input to blank-input halting. Closure of `tm_decidable` under explicitly
realised machine many-one reductions is now verified. Constructing a set-coded
machine that realises the primitive-recursive witness, and the subsequent
code-level reduction to invariance, belong to a later computability layer.
Universality remains a separate infrastructure objective.

The September 8 implementation supplies concrete machines for the entire
primitive-recursive basis (`SC`, `PROJ(i)`, and `CONSTANT(k)`) on arbitrary
argument lists, and a concrete unary realiser for `pr_double`. General `COMP`
and `PREC` compilation remains open. These new base cases do not yet realise
the evaluator or self-hardwiring map, and do not construct internal formulas.
See `Turing_Realisation.thy` and the updated review for the precise boundary.

The October 4 development proves finite-witness closure in the new
`Turing_Models` session. `transitive_zfc_contains_machine`,
`transitive_zfc_contains_configuration`, and `transitive_zfc_contains_trace`
place the actual finite objects in every transitive ZFC set model. The theorem
`transitive_zfc_halting_witness_iff` then characterises external halting by a
certificate belonging to the model. Its recurrence predicate remains the
external `finite_run`; no formula or `sats` equivalence is inferred from this
closure result. The direct route's canonical-run membership obligation is
therefore discharged, while its one-step and formula-adequacy work remains.

## 2. COMPLETION CONTRACT

### 2.1 Machine-parameter adequacy

The first target keeps the machine as a free set parameter and requires no
numbering.

```text
halts_machine_fm in formula
arity(halts_machine_fm) = 1

assumes "transitive_zfc_model(A)"
    and "P in A"
    and "P in machine"
shows
  "(A, [P] satisfies halts_machine_fm) <-> halts_blank(P)"
```

The October development proves the closure theorem removing the explicit
membership premise, in `Turing_Model_Witnesses.thy`:

```text
transitive_zfc_model(A) and P in machine
  ==> P in A.
```

The closure theorem establishes membership of the machine in every model.
Together with the still-open satisfaction theorem above, it would establish
agreement between external execution and internal satisfaction.

### 2.2 Closed indexed halting sentences

`Turing_Coding.thy` now supplies a total decoder and a canonical
natural-number machine code. The second target closes the decoded machine
parameter inside a formula.

```text
e in nat ==> decode_machine(e) in machine
e in nat ==> halt_fm(e) in formula
e in nat ==> arity(halt_fm(e)) = 0

assumes "e in nat"
    and "transitive_zfc_model(A)"
shows
  "(A, [] satisfies halt_fm(e))
     <-> halts_blank(decode_machine(e))"
```

The exact completion criterion is

```text
interpretation concrete_halting:
  halting_sentence halt_fm
```

with all three formula and adequacy obligations derived from definitions. The
numbering layer already proves

```text
machine_numbering_bij:
  machine <-> machine_code

decode_machine_surj:
  nat ->> machine
```

The numeric evaluator over the chosen numbering is now primitive recursive at
the object level. Explicit `prim_rec` witnesses have been verified for the
numeric coding operations used by evaluation, one-step evaluation, finite
iteration, bounded blank-input halting, and natural-code hardwiring. The
verified evaluator and hardwiring witnesses have not yet been connected to the
operational model by a theorem realising the relevant `prim_rec` functions as
set-coded Turing machines. Their graphs have not yet been represented by
first-order formulas inside a transitive model. Closing the formula also
requires a verified quotation of the natural-number parameter `e`.

### 2.3 Boundary of Module III

The semantic equivalence becomes a many-one reduction only after proving

- a concrete natural-number coding of closed formulas
- computability of `e |-> Or(halt_fm(e),sigma)` at formula-code level
- undecidability of blank-input halting for the chosen numbering
- a formal reduction between the corresponding sets of natural-number codes

Surjectivity of a decoder is not sufficient because its enumeration may be
non-computable. Module I now proves

```text
not tm_decidable(self_halting),
```

where each machine receives the unary numeral encoding of its own number.
This does not by itself establish the third item above, because the current
`halting_sentence` interface uses blank-input halting. A finite hardwiring
transformation now proves

```text
M in machine and x in list(symbol) ==>
  (halts_blank(hardwire(M,x)) <-> halts_on(M,x)).
```

The induced self-hardwiring transformation on natural machine codes is now
proved primitive recursive, and its pointwise membership equivalence is
formalised. The remaining obligation is operational: realise the
primitive-recursive transformation by a set-coded Turing machine. Closure of
`tm_decidable` under the resulting machine many-one reduction is already
verified. The realising machine is required before deriving blank-input halting
undecidability. This obligation lies beyond Module III.

## 3. ADEQUACY ROUTES

### 3.1 Primitive-recursive bounded halting

The numeric route starts from the completed function
`code_halts_blank_at(n,e)`. Construct a formula `halts_at_fm` with two free
variables and prove the schematic contract

```text
assumes transitive_zfc_model(A)
    and n in nat
    and e in nat
shows
  (A, [n,e] satisfies halts_at_fm)
    <-> code_halts_blank_at(n,e) = 1.
```

The target closed sentence is then obtained by quoting `e` and existentially
quantifying `n`. The external theorem `halts_blank_iff_code_halts_at` supplies
the final semantic step.

This route requires first-order graph formulas and satisfaction theorems for
the primitive-recursive basis `SC`, `CONSTANT`, `PROJ`, `COMP`, and `PREC`, or
an explicit formula construction for the particular witness
`pr_code_halts_blank_at`. The `PREC` case must be connected to the existing
`is_wfrec_fm` or finite-function infrastructure. The inductive set
`prim_rec` contains semantic functions rather than a canonical syntax tree, so
its membership theorem alone cannot be treated as a formula compiler.

### 3.2 Set-coded one-step adequacy

The first machine-specific theorem is an adequacy theorem for one execution
step. Define a relativised relation `is_step` and a first-order formula
`step_fm` satisfying the schematic contracts

```text
A, env satisfies step_fm(p,c,d)
  <->
is_step(##A, env(p), env(c), env(d))

is_step(##A,P,c,d)
  <->
d = step(P,c).
```

The construction must cover every operation used by `step`: scanning, tape
update, instruction addressing, instruction lookup, list operations,
natural-number arithmetic, and ordered pairs.

Both set-coded constructions of finite computation depend on this theorem.
Reflexive-transitive closure can supply finite-path reasoning, but it cannot
construct or justify the one-step relation.

## 4. AVAILABLE INFRASTRUCTURE

### 4.1 Finite reachability

`Transitive_Models/Rec_Separation.thy` provides

- `rtran_closure_mem_fm`, which describes closure membership by an explicitly
  quantified finite function
- `rtran_closure_fm`, which describes the closure set
- `sats_rtran_closure_mem_fm` and `sats_rtran_closure_fm`

Isabelle's `ZF/Constructible/WF_absolute.thy` provides `rtrancl_closed` and
`rtrancl_abs` in `M_trancl`. The `Independence_CH` interface establishes

```text
M_ZF1_trans < M_trancl "##M".
```

Finite reachability is therefore internalised once the underlying relation is
a set belonging to the model.

### 4.2 Lists and functions

The constructible-model library contains formulas for `Nil`, `Cons`, `hd`,
`tl`, function application, typed functions, and `nth`. It also contains
`length_abs` and `nth_abs` in `M_datatypes`.

Two bridges remain to be supplied.

1. A transitive ZFC model must be connected to `M_datatypes` before the list
   absoluteness lemmas can be used uniformly. The older `Forcing` interface
   supplies a precedent for the sublocale proof.
2. There is no ready-made `length_fm` or formula matching
   `slot(q,b) = 2 * pred(q) + b`. A small local formula layer is required.
   General multiplication is unnecessary because the expression can be
   written as `k + k + b`.

## 5. FINITE-COMPUTATION CONSTRUCTIONS

### 5.1 Direct finite-run formula

The direct construction first mirrors `finite_run` exactly. A formula
`finite_run_fm(P,n,r)` states only that `r` is a relation and a function with
domain `succ(n)`, and that each successor value is obtained by `step_fm` from
the preceding value. It does not impose an initial or final configuration.

The separate formula `halts_machine_fm(P)` then quantifies `n` and `r` and
adds the endpoint conditions from `halts_on_iff_finite_run`: `r` begins at
`initial_config([])` and the state of `r(n)` is `final_state`. Thus
`finite_run_fm` corresponds to `finite_run`, while `halts_machine_fm`
corresponds to blank-input halting. This route requires internalisation of the
finite function, its recurrence condition, and the two endpoint conditions.

### 5.2 Reflexive-transitive closure

The alternative instantiates the existing generic reachability formula

```text
A satisfies Reach(R,x,y)
  <->
<x,y> in rtrancl(R)
```

for `R`, `x`, and `y` belonging to a transitive ZFC model. The machine-specific
relation is then

```text
step_relation(P) = {<c,step(P,c)> . c in configuration}.
```

The remaining obligations are

- `configuration in A`
- `step_relation(P) in A`
- membership in `step_relation(P)` agrees with `step_fm`
- reachability in this relation agrees with `finite_run`

The closure route maximises reuse of `Transitive_Models`; the direct route
matches the present operational theorem more literally. Both share the
one-step adequacy theorem in Section 3.

## 6. IMPLEMENTATION ORDER

The numeric route is the current candidate, because it can reuse the existing
primitive-recursive certificates. Its formula construction and satisfaction
proofs have not yet been implemented; it is not established that this route
is shorter in proof effort than the direct route.

```text
formulae for the primitive-recursive basis
  -> graph-formula closure under COMP and PREC
  -> formula for code_halts_blank_at(n,e)
  -> bounded-predicate satisfaction adequacy
  -> existential halting formula with quoted e
  -> closed halt_fm(e)
  -> interpretation of halting_sentence
```

The alternative set-coded route is

```text
instantiate existing reachability formula
  -> transitive-ZFC bridge for list absoluteness
  -> length and slot formulae
  -> scan, update, fetch, and step formulae
  -> sats_step_fm_iff and step absoluteness
  -> construction and model closure of step_relation(P)
  -> finite reachability and halts_machine_fm
  -> machine-parameter adequacy
  -> machine-code quotation and closed halt_fm(e)
  -> interpretation of halting_sentence
```

If the direct finite-run route is chosen, the generic reachability and
`step_relation` entries are replaced by `finite_run_fm`, its adequacy theorem,
and a closure theorem placing the canonical finite run in the model. The
endpoint conditions are then added by `halts_machine_fm`. The one-step work is
unchanged.

## 7. RELATION TO THE FULL EPQ CONCLUSION

The September [review and roadmap](REVIEW_AND_ROADMAP.md) separates this
module from the full EPQ endpoint. Interpreting `halting_sentence` supplies
semantic adequacy for halting and its negation. Effective formula-code maps
and enumerability infrastructure are still needed for the two halting-based
reductions. The non-arithmeticality conclusion additionally needs effective
translation and absoluteness of arbitrary arithmetic truth, followed by the
non-definability argument. It does not follow solely from this module.

The numerical realisation interface now observes final tape contents modulo
trailing blanks. A literal-list output contract would make general
primitive-recursive realisation impossible; the tape-span obstruction and
its repair are proved in the machine session. This does not alter the raw
`step`, `finite_run`, or numeric evaluator used by the internalisation target.
