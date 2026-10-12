# Theory guide and research boundaries

## 1 Scope

The repository maintains forty theories across five sessions. Nineteen form
[the candidate](../thys/Set_Coded_Halting_Invariance_ZF/ROOT) and twenty-one
form research extensions. Research sessions use the same qualified theory
names as the candidate archive. Each theory has one maintained source.

[Computation](COMPUTATION.md) describes the eight computation theories in
the candidate and the four computation extensions.
[AFP scope](AFP.txt) defines the candidate and its main theorem.
The source of each theorem states its assumptions.

## 2 Internal formulas and invariance

The candidate session extends
[Independence_CH](https://isa-afp.org/entries/Independence_CH.html).
[Turing_Model_Witnesses](../thys/Set_Coded_Halting_Invariance_ZF/Turing_Model_Witnesses.thy)
proves closure of finite computation objects in transitive ZF set models.
[Nat_Membership](../thys/Set_Coded_Halting_Invariance_ZF/Nat_Membership.thy)
provides the internal natural-number domain.
[Turing_Halting_Formula](../thys/Set_Coded_Halting_Invariance_ZF/Turing_Halting_Formula.thy)
constructs the explicit halting formula and proves its satisfaction theorem.
[Turing_Halting_Sentences](../thys/Set_Coded_Halting_Invariance_ZF/Turing_Halting_Sentences.thy)
names machines and inputs to produce closed sentences. Finite closure,
halting satisfaction, and closed halting sentences do not require choice.

[Sentence_Invariance](../thys/Set_Coded_Halting_Invariance_ZF/Sentence_Invariance.thy)
defines invariance across all transitive ZFC set models, proves the
disjunction principle, and obtains CH disagreement witnesses from a
countable transitive ZFC set model.
[Formula_Coding](../thys/Set_Coded_Halting_Invariance_ZF/Formula_Coding.thy)
gives an injective numerical code for formulas.
[Turing_Invariance_Codes](../thys/Set_Coded_Halting_Invariance_ZF/Turing_Invariance_Codes.thy)
defines the target set and proves the semantic coding equivalences.

[Formula_Primrec](../thys/Set_Coded_Halting_Invariance_ZF/Formula_Primrec.thy)
certifies formula constructors.
[Turing_Name_Primrec](../thys/Set_Coded_Halting_Invariance_ZF/Turing_Name_Primrec.thy)
certifies numeral and unary-input names.
[Turing_Machine_Name_Primrec](../thys/Set_Coded_Halting_Invariance_ZF/Turing_Machine_Name_Primrec.thy)
certifies machine names by bounded reverse traversal of their code.
[Turing_Effective_Invariance](../thys/Set_Coded_Halting_Invariance_ZF/Turing_Effective_Invariance.thy)
assembles the two primitive-recursive reductions to the codes of invariant
closed sentences. The direct semantic premise is that CH is not invariant.
The stated countable-model assumption supplies this premise.

## 3 Computation extensions

The [Turing_Computation_Extensions](../thys/Research/Computation/ROOT)
session extends the candidate.
[Turing_Tape](../thys/Research/Computation/Turing_Tape.thy) proves
observational equality for finite tape representations.
[Turing_Evaluator](../thys/Research/Computation/Turing_Evaluator.thy) gives
numeric one-step and finite-step evaluation with exact simulation equations.
[Turing_Evaluator_Primrec](../thys/Research/Computation/Turing_Evaluator_Primrec.thy)
certifies those numeric operations as primitive recursive.
[Turing_Workspace](../thys/Research/Computation/Turing_Workspace.thy) proves
that sufficient blank padding protects saved data for a supplied finite
step bound. These four theories are outside the candidate archive.

## 4 Machine programs

The [Turing_Machines_ZF](../thys/Research/Programs/ROOT) session extends the
computation extensions. Its fourteen theories concern machine
transformations, numerical realization, and concrete programs.

### 4.1 Transformations and reductions

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

### 4.2 Concrete programs and storage

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
protect nearby storage. The workspace theorem avoids dependency on these
program theories.

A general machine compiler for the primitive-recursive COMP and PREC
constructors remains open. The individual programs do not establish those
general cases.

## 5 Arithmetic and model extensions

The [Turing_Models](../thys/Research/Models/ROOT) session extends the candidate.
[Turing_Arithmetic_Truth](../thys/Research/Models/Turing_Arithmetic_Truth.thy)
proves satisfaction rules for the natural-number domain, zero, successor,
order, addition, multiplication, and restricted quantification.
[Turing_Halting_Index](../thys/Research/Models/Turing_Halting_Index.thy)
identifies the model's finite-witness self-halting predicate with the external
self-halting set.

The [Turing_Absoluteness](../thys/Research/Absoluteness/ROOT) session extends
Turing_Models and adds
[Turing_Decidable_Sets](../thys/Research/Absoluteness/Turing_Decidable_Sets.thy).
Its theorem `tm_decidable_in_transitive_model` proves that every set decidable
by the defined machine model belongs to every transitive ZFC set model.

A recursive arithmetic syntax and an effective translation of arbitrary
arithmetic sentences remain open. The existing arithmetic satisfaction rules
do not constitute that translation.

## 6 EPQ boundary

The [EPQ paper](../papers/EPQ.pdf) motivates a reduction from true arithmetic
to codes of sentences invariant across transitive ZFC set models. The
repository proves the self-halting and nonhalting reductions. It does not
establish the general arithmetic-truth reduction, its nonarithmeticality
conclusion, or implementation of every primitive-recursive map by the
repository's machines.

[Build instructions](BUILD.txt) cover the five local sessions.
[Development records](history/README.md) retain earlier claims at their
recorded revisions.
