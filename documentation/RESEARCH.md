# Research extensions

## 1 Boundary

The [candidate library](../thys/Set_Coded_Turing_Machines/ROOT) contains
seventeen theories. Its interfaces are described in the
[library guide](COMPUTATION.md). Twenty-six additional theories in five
research sessions extend that same namespace. Each theory has one
maintained source. The full repository build checks all six sessions.

## 2 Invariance application

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

These reductions do not establish machine undecidability of the target
set in this particular machine model. That conclusion needs a machine
realisation or closure theorem for the reducing functions. It does not
require a reverse reduction. The full arithmetic-truth reduction from the
[EPQ paper](../papers/EPQ.pdf) remains outside the proved results.

## 3 Computation and programs

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

## 4 Model extensions

[Turing_Models](../thys/Research/Models/ROOT) contains arithmetic formulas
and model-restricted halting index sets. Its ZFC interfaces use the
application model predicate.
[Turing_Absoluteness](../thys/Research/Absoluteness/ROOT) proves that every
set decidable by a machine of this model belongs to every transitive ZFC
set model, using an explicit acceptance formula and Separation.

## 5 Interface migration

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
