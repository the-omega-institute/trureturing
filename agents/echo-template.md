# Statement Echo

- Task code:
- Target GID:
- Exact statement:
- Explicit assumptions:
- Dependency GIDs:
- Source anchors:
- Meaning preserved: yes/no
- Ambiguities requiring a new case:
- Remark-closure guard: a claim containing a numerical certificate or an independently testable identity must remain `upgrade-candidate` with `retained_residual: true`; if a Describe remark covers only an explanatory subset, keep the atom `partial/open` and name every testable claim in `unresolved_subitems`.

## Residual Accounting (Required)

- Immediately before publishing a theory batch, run `make echo-residual-summary BASE=origin/dev` from its worktree and paste the complete output block into `.echo-review.md` verbatim; then run `make echo-review-verify BASE=origin/dev` from the same worktree before using the file as evidence.
- Residual counts, mother residual `atom_id` lists, and `unresolved-subitem` lists must never be counted, written, edited, or reordered by hand. They are projections of `digest-status --residual-summary`, which uses the same evaluation as `digest-status --json`.
- After any Lean, Scribe, or `Meta/BACKFILL.yaml` change, discard the earlier block and rerun the target. A stale or manually reconciled block is not publication evidence.
