
## Problems dossier sections (binding)
`tools/StrataLint.Scribe/Problems/ProblemCandidateCatalog.cs` accepts exactly these `##` sections in a `Problems/*.md` dossier, in this order: `Problem`, `Motivation`, `Gap`, `Route`, `Falsifier`, `Evidence`, `Triage`, `ASSUMED-UNVERIFIED`. Any other `##` heading (for example `## Statement echo`) makes the dossier invalid and the resolution claim's slug dangling, and `make emit` / the gate then fail.
- Put additional material under the closest section as a `###` subsection; a statement echo goes under `## Problem` as `### Statement echo`.
- Moving a misplaced heading to a `###` subsection of the right section, with the text unchanged, is an authorized mechanical fix: apply it and continue; it is not a stop condition.
