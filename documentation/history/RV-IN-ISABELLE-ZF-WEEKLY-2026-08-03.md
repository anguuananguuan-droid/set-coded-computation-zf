# RV — IN-ISABELLE-ZF-WEEKLY

Run time: 2026-08-03 06:09:49 +0800

Baseline commit: `21a741943a2592c5f0b7202d974d1150648ff3ee`

## Delivered proof gate

This increment closes semantic finite-input hardwiring. It constructs a loader,
compiles its actions into a machine prefix, shifts the original machine's
non-final control states, proves exact finite-step simulation, and establishes

```text
M in machine and x in list(symbol) ==>
  (halts_blank(hardwire(M,x)) <-> halts_on(M,x)).
```

The endpoint is theorem `hardwire_halts_iff` in
`Turing_Machines_ZF/Turing_Transformations.thy`.

## Requirement map

| Requirement | Implemented state | Verification and validation evidence | Status | Deviation | Residual risk |
| --- | --- | --- | --- | --- | --- |
| Preserve the canonical set-coded machine layer | Existing `Turing_Machine.thy` and `Turing_CH.thy` remain canonical; the new transformation imports the existing decision layer and introduces no duplicate machine semantics | Definition inventory confirms one canonical `machine`, `configuration`, `halts_on`, and `hardwire` definition; final diff contains only the five declared source/document files plus this RV | VERIFIED | None | None |
| Preserve existing user work | The initially modified tracked theory was retained and completed in place; no reset, checkout, deletion, or history rewrite was used | Initial and final `git status`, baseline commit capture, and final diff inspection | VERIFIED | None | None |
| Construct finite input loading and compilation | `loader_actions`, `compile_actions`, `shift_machine`, and `hardwire` are defined with typing, length, fetch, step, and finite-step lemmas | Isabelle kernel accepted `execute_loader_actions`, `steps_compiled_actions`, `fetch_hardwire_shift`, `hardwire_loader_endpoint`, `steps_hardwire_shift`, and `steps_hardwire` | VERIFIED | None | None |
| Prove halting preservation in both directions | `hardwire_halts_iff` proves blank-input halting of the transformed machine exactly when the source machine halts on the fixed input | Clean isolated build of both repository sessions completed with exit code 0 | VERIFIED | None | The induced natural-number code transformation is not yet proved computable |
| Do not use proof escape hatches | No `sorry`, `oops`, `admit`, `axiomatization`, `oracle`, `quick_and_dirty`, or `skip_proofs` occurs in any theory | Repository-wide `rg` scan returned no matches; `git diff --check` passed | VERIFIED | None | None |
| Run the complete Isabelle2025-2/AFP build | `Turing_Machines_ZF` and AFP-backed `Turing_CH` were rebuilt from clean target session state | Isabelle2025-2 `build -c -D .` with an isolated temporary `ISABELLE_HOME_USER`: both sessions finished, exit code 0 | VERIFIED | Shared default session storage was not used for final evidence because concurrent builds repeatedly moved its SQLite database | The temporary isolated build cache is not part of the repository |
| Keep documentation claims aligned with kernel evidence | README, AI disclosure, and the Module III technical note describe semantic hardwiring as complete while retaining the effective code map and blank-input undecidability as open | Documentation diff reviewed against `hardwire_halts_iff` and the absence of a code-effectivity theorem | VERIFIED | `PLAN.md` is absent from the current tree and has no tracked history; README remains the sole canonical roadmap | Future work must not infer blank-input undecidability from semantic hardwiring alone |
| Exclude private and unrelated material | Diff is restricted to the hardwiring proof, the generic final-state monotonicity lemma, aligned documentation, and this RV | Secret/path pattern scan over added lines returned no matches; no untracked build artifacts are present | VERIFIED | None | None |

## Validation

The construction was reviewed along the operational path: a reversed action
list writes the intended input on a blank tape; duplicated instruction slots
make each compiled action independent of the scanned binary symbol; shifted
slots preserve fetch behavior; the loader endpoint equals the shifted original
initial configuration; and final-state absorption rules out a spurious halt
during the loader prefix. These properties jointly validate the user-visible
claim expressed by `hardwire_halts_iff`.

## Open obligations

- Certify the induced map on natural-number machine codes as primitive
  recursive or otherwise computable.
- Transport self-input undecidability to the coded blank-input halting set.
- Continue with finite-run formula internalisation and `sats` adequacy only
  after that proof dependency is closed.
- Formula-code effectivity and the final model-invariance undecidability theorem
  remain outside this increment.

Overall verification state: **VERIFIED**

Overall validation state: **VERIFIED**
