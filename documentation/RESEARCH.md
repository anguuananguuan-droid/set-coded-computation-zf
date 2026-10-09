# Research extensions

## 1 Scope

The independent computation library is described in
[Computation in Isabelle/ZF](COMPUTATION.md). The invariance session proves
the effective self-halting reductions. The three remaining sessions contain
machine-program and model-theoretic extensions. The assumptions of each
theorem are recorded in its source.

## 2 Machine programs

The session [Turing_Machines_ZF](../Turing_Machines_ZF/ROOT) extends the
independent library and uses the bundled ZF-Induct session. Its fourteen
theories concern machine transformations and
concrete programs.

### 2.1 Transformations and reductions

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

### 2.2 Concrete programs

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

## 3 Invariance of set-theoretic sentences

The session [Set_Coded_Invariance_ZF](../Set_Coded_Invariance_ZF/ROOT) extends
the independent library and uses the AFP entry
[Independence of the Continuum Hypothesis](https://www.isa-afp.org/entries/Independence_CH.html).
[Turing_CH](../Set_Coded_Invariance_ZF/Turing_CH.thy) defines invariance across
all transitive ZFC set models and proves the disjunction principle.
[Turing_Halting_Formula](../Set_Coded_Invariance_ZF/Turing_Halting_Formula.thy)
constructs the internal halting formula and proves its satisfaction theorem.
[Turing_Halting_Sentences](../Set_Coded_Invariance_ZF/Turing_Halting_Sentences.thy)
closes the formula with machine and input names.

[Turing_Formula_Coding](../Set_Coded_Invariance_ZF/Turing_Formula_Coding.thy)
gives an injective natural-number code for formulas.
[Turing_Effective_Invariance](../Set_Coded_Invariance_ZF/Turing_Effective_Invariance.thy)
proves that the two maps from a machine code to an invariant-sentence code
are primitive recursive and gives the two many-one reductions under a
countable transitive model assumption. The target is the full set of codes
of invariant closed sentences, not only the constructed sentence family.

The session [Turing_Models](../Turing_Models/ROOT) extends this development.
[Turing_Arithmetic_Truth](../Turing_Models/Turing_Arithmetic_Truth.thy) proves
satisfaction rules for the natural number domain, zero, successor, order,
addition, multiplication, and restricted quantification. A recursive
arithmetic syntax and an effective translation of arbitrary arithmetic
sentences remain open.

## 4 EPQ boundary

The [EPQ paper](../papers/EPQ.pdf) motivates a reduction from true arithmetic
to codes of sentences invariant across transitive ZFC set models. The
repository proves the self-halting and nonhalting reductions; it does not yet
prove the general arithmetic-truth reduction or the resulting
nonarithmeticality statement. It also does not prove that every primitive
recursive map is implemented by the repository's Turing-machine model.

[Reproduction instructions](BUILD.txt) cover the five local sessions.
[Development records](history/README.md) retain earlier claims in their
historical context.
