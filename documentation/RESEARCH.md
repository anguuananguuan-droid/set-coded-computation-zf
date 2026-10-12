# Theory guide and research boundaries

## 1 Scope

The repository maintains forty theories across five sessions. Twelve form
the independent computation library, eleven form the invariance development,
and seventeen form research extensions. The submission manifest selects
nineteen theories from the first two groups.

[Computation](COMPUTATION.md) describes the twelve computation theories.
[AFP scope](AFP.txt) defines the sole candidate and its main theorem.
The source of each theorem states its assumptions.

## 2 Internal formulas and invariance

The [Set_Coded_Invariance_ZF](../thys/Invariance/ROOT) session extends the
computation library and uses
[Independence_CH](https://isa-afp.org/entries/Independence_CH.html).
[Turing_Model_Witnesses](../thys/Invariance/Turing_Model_Witnesses.thy)
proves closure of finite computation objects in transitive models.
[Turing_Nat_Membership](../thys/Invariance/Turing_Nat_Membership.thy)
provides the internal natural-number domain.
[Turing_Halting_Formula](../thys/Invariance/Turing_Halting_Formula.thy)
constructs the explicit halting formula and proves its satisfaction theorem.
[Turing_Halting_Sentences](../thys/Invariance/Turing_Halting_Sentences.thy)
names machines and inputs to produce closed sentences.

[Turing_CH](../thys/Invariance/Turing_CH.thy) defines invariance across all
transitive ZFC set models, proves the disjunction principle, and obtains CH
disagreement witnesses from a countable transitive ZFC set model.
[Turing_Formula_Coding](../thys/Invariance/Turing_Formula_Coding.thy) gives an
injective numerical code for formulas.
[Turing_Invariance_Codes](../thys/Invariance/Turing_Invariance_Codes.thy)
defines the target set and proves the semantic coding equivalences.

[Turing_Syntax_Primrec](../thys/Invariance/Turing_Syntax_Primrec.thy)
certifies formula constructors.
[Turing_Name_Primrec](../thys/Invariance/Turing_Name_Primrec.thy) certifies
numeral and unary-input names.
[Turing_Machine_Name_Primrec](../thys/Invariance/Turing_Machine_Name_Primrec.thy)
certifies machine names by bounded reverse traversal of their code.
[Turing_Effective_Invariance](../thys/Invariance/Turing_Effective_Invariance.thy)
assembles the two primitive-recursive reductions to the codes of invariant
closed sentences. The direct semantic premise is that CH is not invariant.
The stated countable-model assumption supplies this premise.

## 3 Machine programs

The [Turing_Machines_ZF](../thys/Research/Programs/ROOT) session extends the
independent library. Its fourteen theories concern machine transformations,
numerical realization, and concrete programs.

### 3.1 Transformations and reductions

[Turing_Transformations](../thys/Research/Programs/Turing_Transformations.thy)
constructs input loading and hardwiring.
[Turing_Composition](../thys/Research/Programs/Turing_Composition.thy) proves
sequential execution.
[Turing_Reduction](../thys/Research/Programs/Turing_Reduction.thy) defines
numerical output using configuration equivalence and proves decision closure
for reductions whose machine implementation has been supplied.
[Turing_Transformations_Primrec](../thys/Research/Programs/Turing_Transformations_Primrec.thy)
and [Turing_Primrec_Reduction](../thys/Research/Programs/Turing_Primrec_Reduction.thy)
certify the numerical hardwiring map as primitive recursive. The theorem
`self_hardwire_realiser_imp_blank_halting_undecidable` assumes a machine
implementing that map.

### 3.2 Concrete programs and storage

[Turing_Basic](../thys/Research/Programs/Turing_Basic.thy) and
[Turing_Programs](../thys/Research/Programs/Turing_Programs.thy) provide
numerical programs including erasure and successor.
[Turing_Arguments](../thys/Research/Programs/Turing_Arguments.thy) specifies
multiple arguments on a tape.
[Turing_Storage](../thys/Research/Programs/Turing_Storage.thy) and
[Turing_Projection](../thys/Research/Programs/Turing_Projection.thy) support
argument selection.
[Turing_Copy](../thys/Research/Programs/Turing_Copy.thy) proves copying
programs, and [Turing_Arithmetic](../thys/Research/Programs/Turing_Arithmetic.thy)
proves addition and doubling.
[Turing_Realisation](../thys/Research/Programs/Turing_Realisation.thy) relates
machines to initial functions, constants, and projections.

[Turing_Context](../thys/Research/Programs/Turing_Context.thy) proves
`numerical_realisation_does_not_imply_frame`. A machine can implement the
identity function in its prescribed blank context while erasing a saved
cell in a larger context. Numerical correctness alone therefore does not
protect nearby storage. The independent workspace theorem avoids dependency
on these program theories.

A general machine compiler for the primitive-recursive COMP and PREC
constructors remains open. The individual programs do not establish those
general cases.

## 4 Arithmetic and model extensions

The [Turing_Models](../thys/Research/Models/ROOT) session extends invariance.
[Turing_Arithmetic_Truth](../thys/Research/Models/Turing_Arithmetic_Truth.thy)
proves satisfaction rules for the natural-number domain, zero, successor,
order, addition, multiplication, and restricted quantification.
[Turing_Halting_Index](../thys/Research/Models/Turing_Halting_Index.thy)
identifies the model's finite-witness self-halting predicate with the external
self-halting set.

The [Turing_Absoluteness](../thys/Research/Absoluteness/ROOT) session adds
[Turing_Decidable_Sets](../thys/Research/Absoluteness/Turing_Decidable_Sets.thy).
Its theorem `tm_decidable_in_transitive_model` proves that every set decidable
by the defined machine model belongs to every transitive ZFC set model.

A recursive arithmetic syntax and an effective translation of arbitrary
arithmetic sentences remain open. The existing arithmetic satisfaction rules
do not constitute that translation.

## 5 EPQ boundary

The [EPQ paper](../papers/EPQ.pdf) motivates a reduction from true arithmetic
to codes of sentences invariant across transitive ZFC set models. The
repository proves the self-halting and nonhalting reductions. It does not
establish the general arithmetic-truth reduction, its nonarithmeticality
conclusion, or implementation of every primitive-recursive map by the
repository's machines.

[Build instructions](BUILD.txt) cover the five local sessions.
[Development records](history/README.md) retain earlier claims at their
recorded revisions.
