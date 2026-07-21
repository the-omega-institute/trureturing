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

- After the final candidate commit, run `make echo-residual-summary BASE=origin/dev` from its worktree and paste the complete marker-delimited output block into `.echo-review.md` verbatim.
- Residual counts, mother residual `atom_id` lists, and `unresolved-subitem` lists must never be counted, written, edited, or reordered by hand. They are projections of `digest-status --residual-summary`, which uses the same evaluation as `digest-status --json`.
- Immediately before publication, run `make echo-review-verify BASE=origin/dev REVIEW=.echo-review.md`. Publication accepts the residual block only when this byte-level, candidate-and-baseline-snapshot-bound verifier exits zero.
- After any repository or baseline change, discard the earlier block and rerun both targets. Missing, duplicated, stale, reordered, or manually edited blocks are invalid publication evidence.
