# RV — IN-TM-ZF-001

Increment prepared: 2026-08-03 08:12:15 +0800

Final verification run: 2026-08-10 13:15:47 +0800

Baseline commit: `09ff20ff065c916f7d769554f281786eba61af9e`

## Delivered proof gate

This increment closes the operational composition and machine-reduction layer
under the stated machine, configuration, and source-control assumptions.
It constructs a sequential machine that continues after either an explicit
transition to the final state or an implicit out-of-range halt, and proves the
two-phase termination equivalence

```text
sequential_machine(M,N) terminates from c
  <-> M terminates from c and N terminates from the tape left by M.
```

It then defines canonical numerical computation, proves output uniqueness,
and verifies closure of `tm_decidable` under explicitly realised machine
many-one reductions. The primitive-recursive self-hardwiring map is connected
to this layer by the exact remaining premise

```text
tm_realises_unary(R,pr_self_hardwire_code) ==>
  not tm_decidable(blank_halting).
```

The premise has not been discharged. This report evaluates the completed
increment, not the full `IN-TM-ZF-001` mission.

## Requirement map

| Requirement | Implemented state | Verification and validation evidence | Status | Deviation | Residual risk |
| --- | --- | --- | --- | --- | --- |
| Preserve the existing total machine semantics | `sequential_machine` is defined solely from the verified `redirect_final`, state-shifting, list, `fetch`, `step`, and `steps` operations | Definition and import review; Isabelle session build; independent mathematical audit | VERIFIED | None | None |
| Continue after every semantic form of halting | `continuation_prefix` redirects explicit final targets and replaces every missing instruction slot with the same `nop` action followed by handoff | `fetch_sequential_prefix`, `step_sequential_handoff`, and boundary review of explicit and implicit halting, empty tables, and slot bounds | VERIFIED | None | None |
| Prove the first and second phases exactly | The source machine is simulated before halting; handoff has a bounded witness; the continuation machine is simulated under the state shift | `steps_sequential_running`, `steps_sequential_handoff`, `steps_sequential_shift`, and `steps_sequential_after_handoff` accepted by Isabelle | VERIFIED | None | None |
| Prove composition in both directions | Every terminating composed run decomposes into a source termination and a continuation termination, and every such pair composes | `steps_sequential_finalD` and `sequential_machine_terminates_iff`; independent audit checked the handoff bound, natural subtraction, and late halting witnesses | VERIFIED | None | The public theorem is intentionally restricted to well-formed starts in the non-final source control region |
| Define functional numerical computation | `computes_number` requires one exact canonical final configuration containing the unary numeral output | `computes_number_unique` uses final-state absorption and numeral injectivity; independent audit reported no defect | VERIFIED | None | This is a unary interface; multi-argument conventions remain future infrastructure |
| Connect reducers to decision machines | Sequential execution preserves and reflects `yields`, acceptance, and rejection after a computed numerical output | `computes_number_then_yields_iff`, `accepts_number_sequential_iff`, and `rejects_number_sequential_iff` accepted by Isabelle | VERIFIED | None | None |
| Prove many-one closure | `tm_reduces` retains the reducing-machine witness; `tm_many_one_reducible` existentially hides it; decidability and undecidability transport are proved | `tm_many_one_decidable` and `tm_many_one_undecidable`; independent quantifier and direction audit | VERIFIED | None | Only reductions with an actual set-coded machine witness enter this relation |
| Connect primitive-recursive hardwiring without overstating completion | `pr_reduces` is separated from `tm_reduces`; the self-hardwiring PR reduction is unconditional; blank-halting undecidability retains the precise realiser premise | `self_hardwire_pr_reduces`, `self_halting_pr_many_one_reducible_blank_halting`, and `self_hardwire_realiser_imp_blank_halting_undecidable` | VERIFIED | None | The required set-coded machine realiser is not yet constructed |
| Keep documentation aligned with the proof state | README, AI disclosure, and the Module III note record the completed composition and closure results and the isolated realisation gap | Cross-file status review and independent publication-structure audit | VERIFIED | None | Future documentation must distinguish object-level `prim_rec` membership from machine realisability |
| Exclude proof escape hatches and accidental material | No proof bypass, temporary output, credential, private path, or unrelated file is included in the increment | Repository scans, whitespace checks, status inspection, and final diff review | VERIFIED | None | None |
| Rebuild all repository sessions | The machine development and AFP-backed CH application are rebuilt from clean target state | `/Applications/Isabelle2025-2.app/bin/isabelle build -c -j1 -v -D .`; exit code 0 | VERIFIED | None | None |

## Validation

The implementation was reviewed along the complete operational path. Before
the source machine halts, the composed table returns the same instruction. At
the halting transition, the action is preserved and only the target is changed
to the shifted initial state of the continuation. Missing instructions undergo
the same handoff with the original default `nop` action. After handoff, every
step commutes with state shifting. The converse proof locates the bounded
handoff and uses the remaining time to reconstruct the continuation run.

The reduction layer was then validated end to end. A reducer writes one unique
canonical numeral, sequential composition passes that tape to a decider, and
both acceptance and rejection are reflected as equivalences. The resulting
decider proves the intended preimage-closure theorem without assuming a choice
function or a primitive-recursive realisation theorem.

## Open obligations

- Construct a set-coded Turing machine realising `pr_self_hardwire_code`, or
  prove a more general primitive-recursive realisation theorem.
- Derive unconditional blank-input halting undecidability only after that
  operational bridge is verified.
- Construct and verify a universal evaluator machine or an equivalent general
  compiler from a canonical computation model.
- Construct the internal halting formula, prove satisfaction adequacy, and
  formalise formula-code effectivity before claiming invariance
  undecidability.

Overall increment verification state: **VERIFIED**

Overall increment validation state: **VERIFIED**

Full mission state: **PARTIALLY_VERIFIED**
