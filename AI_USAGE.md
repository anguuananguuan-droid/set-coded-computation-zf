# AI assistance

Updated 4 October 2026.

Tang Ziyi formulated the research question, developed the EPQ argument, and
wrote and tested the initial Isabelle formalisation. The project uses
Isabelle/ZF at the author's direction, with the machine semantics kept distinct from
the later model-theoretic application.

OpenAI Codex has made substantial contributions to the retained definitions,
theorem statements, proof scripts, documentation, and build setup. This
includes machine coding and evaluation, the diagonal argument and reduction
infrastructure, the numerical-output repair, the concrete arithmetic and
argument programs, and the workspace and model-witness developments.
These contributions should not be described as proofs written solely by the
human author.

Since August 2026, the author has also authorised autonomous implementation
and verification. A passing build or a published commit does not establish
that the author has reviewed every line or can independently reproduce every proof.
No blanket claim of line-by-line human review is made for these increments.

Earlier work included comments from Anthropic Claude supplied by the author.
The [August disclosure](documentation/history/AI_ASSISTANCE_2026-08.md) retains
the detailed historical record, including the stated roles of the systems used.
Its historical completion claims should be read alongside the current README
and the later correction to the numerical-output contract.

## What is checked

Isabelle checks formal derivability from the definitions and assumptions used.
Builds, concrete examples, and semantic review are separate checks: a valid
proof can still formalise an unsuitable definition. The repository records
both the output-contract defect and the workspace counterexample for that
reason.

The Git history records implementation changes. CI checks the source against
fixed dependencies. Neither automated builds nor AI cross-review constitute
independent expert review, evidence of novelty, or completion of the EPQ's
full theorem.

The EPQ paper itself is unchanged by the September and October development
increments. Its earlier disclosure records AI-assisted criticism, editing,
and preparation of the repository copy, following the author's original
question and manuscript.
