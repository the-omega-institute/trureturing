
## Per-declaration table in the PR body (binding; reviewers reject its absence)
The PR body has one row per delivered declaration (public and private, every lane module), with these columns:
- module;
- name;
- `proof_shape` (`content` or `bind-only`, by the inlining rule of CLAUDE.md §3.2);
- direct frozen dependencies;
- `escape_witness` (the declaration's own, or `none`);
- consumer(s);
- the module's `admission_basis`.

**Direct frozen dependencies.** List each frozen D5 declaration used on the declaration's live proof path, with every same-delivery helper inlined, as declaration `GID` + declaration `statement_id`, or write `none`.
- Generate the column by script from the elaborated proof terms (`Lean.Expr.getUsedConstants` on each declaration's value, followed through same-delivery helpers).
- Map the constants to their declaration `statement_id`s in the Lean report (`.lake/build/stratalint/raw-lean-report.json`) built at the merged dev base, keeping only constants of modules that have a state record `Golden/Frozen/state/<module>.lean.json`.
- Never use a module pin for a declaration identity.
- Pinned Mathlib declarations are not frozen dependencies. Name the decisive ones in the `proof_shape` reason instead.

The Lean comment block's labels agree with the table row by row.
