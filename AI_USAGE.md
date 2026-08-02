# AI Assistance Disclosure

Tang Ziyi, Version 0.2, August 2026

## Purpose

This statement records substantive use of generative AI during the development
of this repository. It identifies the systems used, the work they assisted,
the extent of human control, and the checks applied to retained material.

## Human contribution and formal development

Tang Ziyi developed the argument presented in his EPQ paper. Drawing on that
work, his study of mathematical logic and Turing machines, and his analysis of
[Turing's original paper](https://doi.org/10.1112/plms/s2-42.1.230), he
formulated the research problem, the governing formalisation framework, and
the high-level three-module architecture of this project.

The formal development began with an initial Isabelle version written and
tested by Tang Ziyi. OpenAI Codex then assisted substantially in revising and
extending that source into the present version. Tang Ziyi continued to work
directly in Isabelle, reviewed the retained definitions and theorem structure,
and edited portions of the source. Anthropic Claude Opus was used for
second-model cross-review.

On 2 August 2026, Tang Ziyi authorised Codex to continue the remaining
formalisation as a sequence of independently implemented, kernel-checked
weekly increments. Later development commits may therefore be implemented,
verified, and pushed by Codex under the standing research and design
constraints before line-by-line human review. The commit history and this
disclosure distinguish those increments from the author's earlier direct
formal work.

The design requirements and architectural choices explicitly set by Tang Ziyi
included

- using Isabelle/ZF and representing the machine as sets in the same
  foundational setting as the later model-theoretic application
- treating the reusable Turing-machine semantics as the primary development
  and the CH result as a separate application
- selecting a minimal deterministic binary machine, a two-list tape
  representation, and total operational semantics
- requiring a visible dependency chain, realised in the retained theory from
  representation and typing through `scan`, `update`, `fetch`, `step`, `steps`,
  `finite_run`, and `halts_on`
- isolating the unimplemented internal halting formula and its adequacy theorem
  instead of presenting them as completed results
- requiring human-readable Isabelle source with restrained naming, regular
  indentation, balanced theorem blocks, and no redundant lemmas or explanatory
  prose

These constraints governed the candidate implementations produced with Codex
and the subsequent decisions to retain, rewrite, simplify, or remove them.
Substantial Codex-generated or Codex-drafted definitions, theorem statements,
and proof scripts are retained in both Isabelle theories.

## Policy basis

The [ITP 2026 proceedings](https://itp-conference-2026.github.io/) are published
in LIPIcs. The relevant publisher policy is therefore
[Dagstuhl Publishing's GenAI policy](https://drops.dagstuhl.de/docs/gen-ai),
which permits assisted research and writing, requires substantive use to be
declared, and leaves ethical, legal, and intellectual responsibility with the
human author. The
[ACM authorship policy](https://www.acm.org/publications/policies/new-acm-policy-on-authorship)
and
[Springer Nature's AI guidance](https://group.springernature.com/gp/group/ai/ai-guidance-for-our-researchers-and-communities)
are cited as corroborating standards, not as ITP policies. They apply the same
principles of disclosure, human authorship, and accountability.

The project's proof-engineering practice was also informed by Lawrence C.
Paulson's AITPM talk of 8 April 2026,
[*AI and Isabelle: Experiences and Perspectives*](https://aitpm.github.io/slides/Paulson.pdf).
Paulson presents AI as an interactive assistant while requiring generated
proofs to be inspected and made readable. This is a methodological influence,
not a publication policy.

## Systems used

| System | Period | Role |
| --- | --- | --- |
| OpenAI Codex using GPT-5.6-sol | 10 July-2 August 2026 | Author-directed and, from 2 August, standing-authorised work on Isabelle and AFP source inspection, proof planning, formal implementation, build diagnosis, refactoring, documentation, and release checks |
| Anthropic Claude Opus 4.8 | July 2026 | Second-model cross-review of mathematical scope, locale assumptions, completion claims, and presentation |

Claude's comments were supplied to the development process by the author.
They were treated as review proposals and adopted selectively. Claude did not
edit repository files or run Isabelle.

## Scope of assistance

| Artifact | AI assistance | Author control | Verification |
| --- | --- | --- | --- |
| `Turing_Machine.thy` | Codex assisted in extending and revising definitions, theorem statements, proof scripts, names, and theory structure from the initial development into the retained theory | Tang Ziyi wrote and tested the initial formalisation, set the model and structural constraints, reviewed the retained semantic structure, and directly revised portions of the theory | Isabelle2025-2 build |
| `Turing_Coding.thy` | Codex inspected the Isabelle/ZF and AFP coding libraries, implemented the first instruction-stream encoding, diagnosed proof search, and replaced an unstable automated step with an explicit equality argument | Tang Ziyi authorised the machine-numbering programme and fixed the requirements of minimality, readability, and effective reuse; this increment was implemented under his standing direction rather than line-by-line co-written by him | Isabelle2025-2 build |
| `Turing_CH.thy` | Codex assisted in constructing the locale interface, the general invariance theorem, the CH instance, and their proofs; Claude supplied cross-review of assumptions and completion claims | Tang Ziyi developed the EPQ reduction, fixed its formal scope, directed its implementation, and decided which conditional claims to retain | Isabelle2025-2 and AFP build |
| `TURING_INTERNALISATION.md` | Codex inspected Isabelle and AFP sources and assisted in constructing the technical route; Claude cross-reviewed the boundary of the missing theorem | Tang Ziyi determined the target, scope, and final structure and directly revised the text | Design specification only; Module III is not implemented |
| `README.md` and release files | Codex assisted in drafting, restructuring, and auditing the documentation, build configuration, file selection, licensing presentation, and PDF metadata | Tang Ziyi set the release standard, directed the revisions, edited the text, and approved the public structure | Build, link, file-tree, and formatting checks |
| EPQ paper | AI assisted criticism, editorial revision, presentation checks, and preparation of the repository copy | Tang Ziyi formulated the research question and wrote the original manuscript; he selected the final argument and text | PDF compilation and visual inspection; no expert peer review |

## Human review and verification

- Tang Ziyi is the sole human author and accepts responsibility for every
  released claim, proof, document, and citation. AI systems are not authors.
- The retained theories build with Isabelle2025-2 and the AFP snapshot dated
  6 February 2026. Kernel acceptance is used as a check of formal derivability,
  not as evidence of novelty or of the adequacy of unfinished interfaces.
- Mathematical status is stated explicitly. In particular, the internal
  halting formula, its adequacy theorem, machine numbering, universality, and
  halting undecidability are not claimed as completed.
- External references and library claims retained after AI-assisted work were
  checked against the cited sources or the installed Isabelle and AFP source
  during the release audit. The author remains responsible for their accuracy.
- No confidential third-party manuscript or peer-review material was supplied
  to an AI system.

This repository has not yet received independent expert review. Any later
submission will follow the disclosure requirements of its specific venue.
