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

- Immediately before publishing a theory batch, run `make echo-residual-summary BASE=origin/dev` from its worktree and replace `Generated/echo-residual-summary.md` with the complete output bytes.
- Residual counts, mother residual `atom_id` lists, and `unresolved-subitem` lists must never be counted, written, edited, or reordered by hand. They are projections of `digest-status --residual-summary`, which uses the same evaluation as `digest-status --json`.
- After any Lean, Scribe, theory-source, or `Meta/Digestion/backfill/**` change, discard the earlier projection and rerun the target. A stale or manually reconciled block is not publication evidence.
