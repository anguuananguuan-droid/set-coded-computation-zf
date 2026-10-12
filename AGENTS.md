ENGINEERING RULES

1 AUTHORITY AND SCOPE

1.1 Changes shall follow the project owner's authorized scope. The sole AFP
candidate is specified in documentation/AFP.txt. Research extensions shall
remain outside its dependency closure unless a scope change is approved.

1.2 Within authorized scope, routine decomposition, reversible local edits,
dependency checks, builds, and export may proceed without renewed approval.

1.3 AFP submission and messages to reviewers require explicit authorization
from the project owner.

1.4 Private notes and conversations shall not be copied into public sources,
documents, or records. Untracked files shall not be adopted or published
without authorization.

2 SOURCE STRUCTURE

2.1 Maintained theories shall have one source under thys. The submission
archive shall be generated from submission/ROOT. Generated copies shall not
be edited as maintained sources.

2.2 Each theory shall have a Title and Author header, one theory-level
section, and subordinate subsections. A heading shall state the scope of the
content that follows it.

2.3 Definitions shall precede their use. Public interfaces shall state their
object domains and necessary assumptions. A conditional theorem shall not
be described as an unconditional result.

3 NAMES AND NOTATION

3.1 A theory name shall match its file basename. Existing theory and session
names shall be preserved unless a checked interface change requires a rename.
New theory names shall use the established word-separated underscore form.

3.2 Constants and facts shall use descriptive lowercase names separated by
underscores. Predicate equivalences shall use the suffix _iff. Domain facts
shall use _type where consistent with the existing interface.

3.3 Primitive-recursive certificates shall use pr_ followed by the operation
name. Their membership and value facts shall use _in_prim_rec and _apply.
Certificate membership shall not be described as machine implementation.

3.4 A variable shall retain one mathematical role within a statement. Use n
and k for natural indices, e for codes, c for configurations, and p and q for
formulas where these names are available. Existing formal conventions may be
retained when their meaning is explicit.

3.5 Reuse the established Isabelle symbols and notation. New notation shall
have one stated meaning and shall not conceal an assumption or representation.

4 INTERFACES AND VERIFICATION

4.1 A changed definition, import, theorem name, or assumption shall receive a
dependency check. Source moves shall update session manifests and documents.
Routine proof changes shall receive an affected-session build.

4.2 Submission changes shall be checked on the exported archive. Acceptance
checks shall exercise its declared timeout, inspect proof dependencies,
validate the linter with negative controls, and produce both PDF variants.
Document references shall converge and the final PDFs shall have no overfull
boxes. PDF checks shall compare extracted text with the declared text bounds
and inspect the final compiler logs.

4.3 A successful build shall be reported only for the revision actually
checked. Source scans, kernel proof checks, document checks, and mathematical
review shall not be treated as interchangeable evidence.

5 DOCUMENTS AND RECORDS

5.1 Documents shall use a numbered hierarchy recoverable in plain text.
Titles shall identify their scope. Equal logical levels shall have equal
form. Colour, icons, ornament, and promotional language shall not encode
meaning.

5.2 Public prose shall describe the mathematics and engineering facts needed
to use or assess the work. It shall omit conversational context and claims
unsupported by the recorded evidence.

5.3 Records shall identify their date, source revision, verified claims, and
remaining limitations. Historical records shall not be overwritten to match
a later state. Corrections shall identify the superseded claim and its new
evidence in a subsequent record.

5.4 Attribution and license notices shall be preserved. Legal text shall not
be reformatted or rewritten to satisfy stylistic preferences.
