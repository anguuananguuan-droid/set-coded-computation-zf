# Research extensions

## 1 Scope

The [candidate library](../thys/Set_Coded_Turing_Machines/ROOT) contains
seventeen theories. Its interfaces are described in the
[library guide](COMPUTATION.md). Twenty-six additional theories in five
research sessions extend that same namespace. Each theory has one
maintained source. The full repository build checks all six sessions.

The candidate establishes a reusable connection between finite machine
execution and internal satisfaction. The wider project also seeks the
arithmetic-truth reduction in Section V of the [EPQ paper](../papers/EPQ.pdf)
and general machine implementations of numerical constructions. These
research objectives remain active. Completing the candidate does not
complete them. This document distinguishes proved interfaces from the
remaining mathematical obligations.

## 2 Established results

### 2.1 Halting formulas

The candidate constructs `halt_fm` as an element of Isabelle/ZF's
first-order `formula` datatype. `halt_fm_type`, `arity_halt_fm_eq`, and
`sats_halt_fm` establish its syntax, two-variable interface, and meaning.
`halt_sentence_type`, `arity_halt_sentence`, and `sats_halt_sentence_iff`
give an explicit closed sentence for each well-formed machine and finite
input, with truth equivalent to external halting in every transitive ZF
set model. The model is an assumption. Existence of such a model is not a
conclusion. No assumed halting-satisfaction interface remains in this proof.

`pr_machine_input_sentence_code_in_prim_rec` and
`pr_machine_input_sentence_code_apply` certify construction of the exact
sentence code from a machine code and unary natural input. These are
numerical primitive-recursion certificates, not machine implementations.

### 2.2 Invariance

[Turing_Invariance](../thys/Research/Invariance/ROOT) contains six theories.
`Turing_Decidability` specifies scanned-symbol decision semantics.
`Turing_Rejection` proves self-input halting undecidable by a concrete
machine transformation. `Turing_Primrec_Reductions` defines numerical
primitive-recursive reducibility.

`Sentence_Invariance` defines agreement across all transitive ZFC set
models. CH disagreement follows from the existence of a countable
transitive ZFC set model. `Turing_Invariance_Codes` gives the semantic code
equivalences. `Turing_Effective_Invariance` proves primitive-recursive
reductions from self-input halting and its complement to invariant
sentence codes, through the generic theorem `pr_reduces_invariance`.

The membership equivalences in these reductions hold in both directions.
The missing connection to `tm_decidable` is a machine implementation of a
reducing function. A realiser for the positive map is sufficient to transfer
self-halting undecidability using `realised_pr_reduction` and
`tm_many_one_undecidable`. A general primitive-recursive realisation theorem
would also suffice. No reverse reduction from invariance to halting is
required.

### 2.3 Evaluation and programs

[Turing_Computation_Extensions](../thys/Research/Computation/ROOT) contains
three theories. `Turing_Evaluator` proves numerical simulation of one step
and finite execution. `Turing_Evaluator_Primrec` certifies the numerical
functions. `Turing_Workspace` proves preservation of saved external data
for a supplied finite step bound and sufficient blank padding.

[Turing_Machines_ZF](../thys/Research/Programs/ROOT) contains fourteen
theories for transformations, sequential execution, numerical realization,
copying, arithmetic, argument storage, and projection. `Turing_Context`
exhibits the difference between standalone correctness and preservation
of surrounding data. General composition and primitive-recursion
compilation remain open. The numeric evaluator is not implemented by a
verified universal machine.

### 2.4 Model extensions

[Turing_Models](../thys/Research/Models/ROOT) contains arithmetic formulas
and model-restricted halting index sets. Its ZFC interfaces use the
application model predicate.
[Turing_Absoluteness](../thys/Research/Absoluteness/ROOT) proves that every
set decidable by a machine of this model belongs to every transitive ZFC
set model, using an explicit acceptance formula and Separation.

## 3 Arithmetic-truth reduction

Section V of the EPQ paper translates each arithmetic sentence theta
directly to a set-theoretic sentence theta-omega. Its quantified variables
range over the model's standard natural numbers. A fixed non-invariant
sentence sigma then gives the map from the code of theta to the code of
`Or(theta-omega,sigma)`. Invalid arithmetic sentence codes map to the code
of sigma. This construction does not require a universal Turing machine.

[Turing_Arithmetic_Truth](../thys/Research/Models/Turing_Arithmetic_Truth.thy)
currently supplies the meanings of zero, successor, order, addition,
multiplication, and natural-number-restricted quantifiers. It does not
define a source arithmetic language or prove translation correctness for
arbitrary sentences. The following obligations remain.

### 3.1 Syntax and truth preservation

Define the arithmetic source syntax, its standard-natural-number semantics,
and a recursive translation into `formula`. Prove formula membership,
free-variable bounds, and satisfaction equivalence by structural induction.
The closed instance must state that every transitive ZF set model satisfies
the translated sentence exactly when it is true in the standard natural
numbers. Atomic and quantifier lemmas alone do not establish this theorem.

### 3.2 Effective codes and reduction

Define natural-number codes of source sentences and certify recognition of
valid closed codes. Prove a total primitive-recursive translation on codes,
including its exact agreement with the syntactic translation. Extend the
sentence family on invalid codes by a false sentence, then apply
`pr_reduces_invariance`. A direct implementation may instead return sigma
on invalid codes, as in the paper. Both constructions require proof of the
invalid-code case.

The resulting source set is the set of codes of true arithmetic sentences.
The target is `invariant_formula_codes`. A fixed non-invariant closed
sentence remains a necessary premise. For the CH instance, the existing
countable-transitive-ZFC-model hypothesis supplies that premise.

### 3.3 Non-arithmeticity

The paper additionally uses Tarski's undefinability theorem and closure of
arithmetical sets under computable preimages. To formalise this corollary
under the paper's model-existence hypothesis requires checked theorems for
the chosen syntax, semantics, and reducibility.
These results are not supplied by the current research theories. Proving
the reduction alone does not complete this final corollary.

Full arithmetic truth cannot be reduced by a total computable map to
ordinary machine halting. Halting is computably enumerable, whereas full
arithmetic truth is not arithmetical. The direct translation above preserves
truth without computing it. It therefore has no such obstruction.

## 4 Machine realisation

[Turing_Realisation](../thys/Research/Programs/Turing_Realisation.thy)
provides concrete base programs. General compilation still requires
closure under `COMP` and `PREC`, including preservation of arguments and
intermediate results. Sequential composition of two machines is already
proved, but does not provide arbitrary multi-argument composition.

`numerical_realisation_does_not_imply_frame` proves that a standalone
numerical contract does not protect saved neighbouring data.
`steps_preserve_frame` supplies protection for a given finite step bound
and sufficient margin. It does not select a computable runtime bound for
an arbitrary terminating program. A general compiler must supply a storage
or simulation invariant that remains valid throughout its subcomputations.

A universal machine requires a concrete machine interpreter and a theorem
relating its execution to the encoded machine's execution and halting.
`code_steps_correct` and the primitive-recursive evaluator certificates
are numerical results. They do not yet supply this machine or its unbounded
execution loop. Compiler completion, universal simulation, and the direct
arithmetic translation are distinct obligations.

## 5 Verification and completion

[RV.010](records/RV.010.txt) records the whole-repository audit at
6c1b42c. The successful build checks all present proofs. It does not check
the unimplemented obligations in sections 3 and 4.

The next EPQ milestone is section 3.1. Its acceptance condition is the
structural truth-preservation theorem with no assumed translation-correctness
interface. Section 3.2 then establishes the effective reduction. Section
3.3 closes the stronger conclusion of the paper. Machine realisation remains
a separate research objective and is required when transferring numerical
reductions to this repository's `tm_decidable` predicate.

## 6 Interface migration

The previous candidate namespace was `Set_Coded_Halting_Invariance_ZF`.
Maintained clients now import `Set_Coded_Turing_Machines` for machine,
coding, tape, and halting-formula theories. The application theories listed
in section 2 are qualified by `Turing_Invariance`.

`numeral_input` and its domain, length, and injectivity facts now belong to
`Turing_Machine`. The primitive-recursive halting-code constructor belongs
to `Turing_Halting_Codes`. `Turing_Model_Witnesses` imports the machine
semantics directly. The ZFC model predicate belongs to `Sentence_Invariance`.
The old qualified constant names change with their defining theory. This
migration precedes AFP submission and is recorded explicitly for local
clients.
