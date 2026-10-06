# Research extensions

## 1 Scope

The independent computation library is described in
[Computation in Isabelle/ZF](COMPUTATION.md). The following three sessions
extend the repository beyond that library. They contain proved results and
open interfaces. The assumptions of each theorem are recorded in its source.

## 2 Machine programs

The session [Turing_Machines_ZF](../Turing_Machines_ZF/ROOT) extends the
independent library and uses the bundled ZF-Induct session. Its sixteen
theories concern arithmetic certificates, machine transformations, and
concrete programs.

### 2.1 Arithmetic certificates

[Turing_Primrec](../Turing_Machines_ZF/Turing_Primrec.thy) proves primitive
recursive certificates for the numeric coding operations.
[Turing_Evaluator_Primrec](../Turing_Machines_ZF/Turing_Evaluator_Primrec.thy)
extends these certificates to finite numeric evaluation. Membership in the
formal class of primitive recursive functions does not itself supply a
finite machine implementing the function.

### 2.2 Transformations and reductions

[Turing_Transformations](../Turing_Machines_ZF/Turing_Transformations.thy)
constructs input loading and hardwiring.
[Turing_Composition](../Turing_Machines_ZF/Turing_Composition.thy) proves
sequential execution.
[Turing_Reduction](../Turing_Machines_ZF/Turing_Reduction.thy) defines
numerical output using configuration equivalence and proves decision closure
under reductions for which a machine implementation has been supplied.

[Turing_Transformations_Primrec](../Turing_Machines_ZF/Turing_Transformations_Primrec.thy)
and [Turing_Primrec_Reduction](../Turing_Machines_ZF/Turing_Primrec_Reduction.thy)
certify the natural code hardwiring map as primitive recursive. The theorem
`self_hardwire_realiser_imp_blank_halting_undecidable` still assumes a machine
implementing that map. It is a conditional result about blank input halting.

### 2.3 Concrete programs

[Turing_Basic](../Turing_Machines_ZF/Turing_Basic.thy) and
[Turing_Programs](../Turing_Machines_ZF/Turing_Programs.thy) provide basic
numerical programs, including erasure and successor.
[Turing_Arguments](../Turing_Machines_ZF/Turing_Arguments.thy) specifies
multiple arguments on one tape.
[Turing_Storage](../Turing_Machines_ZF/Turing_Storage.thy) and
[Turing_Projection](../Turing_Machines_ZF/Turing_Projection.thy) support
selection of an argument.
[Turing_Copy](../Turing_Machines_ZF/Turing_Copy.thy) proves copying programs,
and [Turing_Arithmetic](../Turing_Machines_ZF/Turing_Arithmetic.thy) proves
addition and doubling.
[Turing_Realisation](../Turing_Machines_ZF/Turing_Realisation.thy) relates
concrete machines to initial functions, constants, and projections.

A general machine compiler for primitive recursive composition and recursion,
the COMP and PREC constructors, remains open. The individual programs do not
establish those general cases.

[Turing_Context](../Turing_Machines_ZF/Turing_Context.thy) proves
`numerical_realisation_does_not_imply_frame`. A machine can compute the
identity function on its prescribed blank input context while erasing a
saved cell in a larger context. This counterexample explains why numerical
correctness alone is insufficient for safe storage during composition.
The independent workspace theorem does not depend on these program theories.

## 3 Models and internal formulas

The session [Turing_CH](../Turing_CH/ROOT) extends the independent library
and uses the AFP entry
[Independence of the Continuum Hypothesis](https://www.isa-afp.org/entries/Independence_CH.html).
Its [theory](../Turing_CH/Turing_CH.thy) proves `uniform_or_invariant_iff`, a
disjunction principle for a sentence whose truth is uniform across the
specified models. Assuming a countable transitive ZFC set model exists, CH
provides a fixed sentence whose truth differs between such models.

The locale `halting_sentence` assumes `sats_halt_fm_iff`, the correspondence
between an internal formula's satisfaction and external machine halting.
The formula and its correctness proof have not been constructed. Results
using this locale remain conditional on that interface.

The session [Turing_Models](../Turing_Models/ROOT) extends Turing_CH.
[Turing_Model_Witnesses](../Turing_Models/Turing_Model_Witnesses.thy) proves
that finite machines, configurations, and canonical traces belong to every
transitive ZFC set model. Its halting witness theorem uses the external
predicate `finite_run`. Membership of a trace in a model does not prove
correctness of an internal formula describing that trace.

[Turing_Arithmetic_Truth](../Turing_Models/Turing_Arithmetic_Truth.thy) proves
satisfaction rules for the natural number domain, zero, successor, order,
addition, multiplication, and restricted quantification. A recursive
arithmetic syntax and an effective translation of arbitrary arithmetic
sentences remain open.

## 4 EPQ boundary

The [EPQ paper](../papers/EPQ.pdf) motivates an effective reduction from true
arithmetic to codes of sentences invariant across transitive ZFC set models,
under a model existence assumption. That reduction and the resulting
nonarithmeticality theorem have not been fully formalised here. A direct
arithmetic translation need not pass through a universal machine, but it
still requires a complete translation and its satisfaction proof.

The repository contains twenty seven theories in four sessions, eight in
the independent library, sixteen in the extended machine session, one in
Turing_CH, and two in Turing_Models.
[Reproduction instructions](BUILD.txt) cover all four.
[Development records](history/README.md) retain earlier claims in their
historical context.
