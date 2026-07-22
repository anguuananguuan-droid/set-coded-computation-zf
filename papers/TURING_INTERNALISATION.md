# INTERNALISING TURING-MACHINE COMPUTATION IN ISABELLE/ZF

Tang Ziyi, Technical Design Note, July 2026

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

Module III ends with a concrete interpretation of `halting_sentence`.
Universality, halting undecidability, and an effective reduction to invariance
belong to a later computability layer.

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

A closure theorem should then remove the explicit membership premise.

```text
transitive_zfc_model(A) and P in machine
  ==> P in A.
```

This establishes that a set-coded machine has the same finite computation in
the external semantics and in every transitive set model of ZFC.

### 2.2 Closed indexed halting sentences

The second target defines a decoder and closes the machine parameter inside a
formula.

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
  halting_sentence decode_machine halt_fm
```

with all four locale obligations derived from definitions.

A decoder alone is not a machine numbering. A reusable numbering additionally
requires an encoder and a coverage theorem such as

```text
P in machine ==> encode_machine(P) in nat
P in machine ==> decode_machine(encode_machine(P)) = P.
```

Closing the formula also requires a verified quotation of the natural number
or hereditarily finite set representing the decoded machine.

### 2.3 Boundary of Module III

The semantic equivalence becomes a many-one reduction only after proving

- effective encodings of machines and closed formulas
- computability of `e |-> Or(halt_fm(e),sigma)` at formula-code level
- undecidability of blank-input halting for the chosen numbering
- a formal reduction between the corresponding sets of natural-number codes

Surjectivity of a decoder is not sufficient because its enumeration may be
non-computable. These obligations lie beyond Module III.

## 3. ONE-STEP ADEQUACY

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

Both candidate constructions of finite computation depend on this theorem.
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

The alternative first proves a generic reachability formula

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

```text
generic reachability formula
  -> transitive-ZFC bridge for list absoluteness
  -> length and slot formulae
  -> scan, update, fetch, and step formulae
  -> sats_step_fm_iff and step absoluteness
  -> construction and model closure of step_relation(P)
  -> finite reachability and halts_machine_fm
  -> machine-parameter adequacy
  -> decoder, quotation, and closed halt_fm(e)
  -> interpretation of halting_sentence
```

If the direct finite-run route is chosen, the generic reachability and
`step_relation` entries are replaced by `finite_run_fm`, its adequacy theorem,
and a closure theorem placing the canonical finite run in the model. The
endpoint conditions are then added by `halts_machine_fm`. The one-step work is
unchanged.
