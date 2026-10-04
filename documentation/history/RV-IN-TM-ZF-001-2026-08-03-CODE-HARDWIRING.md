# RV — IN-TM-ZF-001

Run time: 2026-08-03 06:51:40 +0800

Baseline commit: `7b14efc4c0ca06fe654bdc3ce2ffda60e730f7bb`

## Delivered proof gate

This increment closes primitive-recursive natural-code hardwiring. It proves
that the code transformer agrees exactly with the previously verified
set-coded machine construction:

```text
e in nat and n in nat ==>
  hardwire_code(e,n)
    = encode_machine(
        hardwire(decode_machine(e),numeral_input(n))).
```

It supplies explicit Isabelle/ZF `prim_rec` witnesses for the machine shift,
loader prefix, hardwiring map, and diagonal self-hardwiring map. The resulting
pointwise reduction is

```text
e in nat ==>
  (e in self_halting
    <-> self_hardwire_code(e) in blank_halting).
```

The endpoint is theorem `self_hardwire_reduction` in
`Turing_Machines_ZF/Turing_Transformations_Primrec.thy`.

## Requirement map

| Requirement | Implemented state | Verification and validation evidence | Status | Deviation | Residual risk |
| --- | --- | --- | --- | --- | --- |
| Preserve the canonical set-coded semantics | The new theory imports the existing semantic transformation and numeric evaluator; no duplicate machine semantics or hardwiring semantics was introduced | Import graph and definition inventory reviewed; complete repository build passed | VERIFIED | None | None |
| Traverse arbitrary natural machine numbers safely | `length_nat_list_decode_le` bounds the decoded list by its natural code; instruction codes are normalised before shifting | Isabelle accepted the single-pass `code_shift_machine_aux_correct` invariant for every `e in nat`; independent mathematical audit reported no P0, P1, or P2 defect | VERIFIED | None | None |
| Construct the numeral loader at code level | `code_loader_prefix` builds the exact instruction-code prefix used by semantic `hardwire`, with the tail machine shifted by twice the numeral length | Isabelle accepted `code_loader_prefix_correct`; audit checked block order, targets, reverse indexing, and the `2*n` state offset | VERIFIED | None | None |
| Prove code and semantic hardwiring commute | `hardwire_code_correct` and `decode_hardwire_code` identify numeric and set-coded transformations | Kernel acceptance in the clean build and independent proof-chain review | VERIFIED | None | None |
| Certify the transformation primitive recursive | Explicit witnesses culminate in `pr_hardwire_code_in_prim_rec` and `pr_self_hardwire_code_in_prim_rec`, with application theorems on arbitrary natural tails | Isabelle accepted every `prim_rec` typing and application theorem; audit checked `COMP`, `PREC`, and `PROJ` argument order | VERIFIED | None | No theorem yet realises every relevant `prim_rec` function by a set-coded Turing machine |
| Reduce self-input membership to blank-input membership | `blank_halting` is defined in the decision-language layer and `self_hardwire_reduction` proves the pointwise equivalence | Isabelle kernel acceptance and independent equivalence-chain review | VERIFIED | None | This is not yet a `tm_decidable` preimage-closure theorem, so blank-input halting undecidability is not claimed |
| Keep source minimal and readable | Machine shifting uses one bounded reverse-index fold; generic double reversal, the unused numeral codec, a duplicate state-shift alias, and a single-use global map lemma were removed | AFP-facing source review found no P0 or P1 issue; all retained public correctness, decoding, codomain, PR-witness, and reduction results have distinct roles | VERIFIED | Public names `hardwire_code` and `code_loader_prefix` remain concise rather than spelling out `numeral` | Their theorem statements make the numeral-input contract explicit |
| Keep documentation aligned with proof status | README, AI disclosure, ROOT, and the Module III note now record the completed primitive-recursive map and the missing operational bridge | Final documentation audit findings were repaired; local file inventory and links checked | VERIFIED | None | Future work must preserve the distinction between primitive recursiveness and realisability by this TM model |
| Exclude proof escape hatches and private material | No proof bypass, local absolute path, credential, email address, temporary artifact, or unrelated file is present in the release diff | Repository-wide pattern scans and `git diff --check` produced no findings | VERIFIED | None | None |
| Rebuild all repository sessions | Both the machine development and AFP-backed CH application were rebuilt from clean target state | `/Applications/Isabelle2025-2.app/bin/isabelle build -c -j1 -v -D .`; `Turing_Machines_ZF` and `Turing_CH` finished; exit code 0 | VERIFIED | None | None |

## Validation

The implementation was reviewed along the complete semantic path. Natural
instruction streams are decoded and normalised, shifted without changing
instruction order, prefixed by the exact loader compiled in the semantic
theory, and decoded back to `hardwire(decode_machine(e),numeral_input(n))`.
Diagonal substitution then maps each self-input instance to one canonical
blank-input machine code. This validates the claimed primitive-recursive
number transformation and its membership equivalence.

## Open obligations

- Prove that the required object-level primitive-recursive transformations are
  realised by set-coded Turing machines, or prove the corresponding closure of
  `tm_decidable` under their preimages.
- Derive `not tm_decidable(blank_halting)` only after that bridge is verified.
- Continue with a universal evaluator or an equivalent general realisation
  theorem.
- Construct the internal halting formula, prove satisfaction adequacy, and
  formalise the formula-code reduction before claiming invariance
  undecidability.

Overall verification state: **VERIFIED**

Overall validation state: **VERIFIED**
