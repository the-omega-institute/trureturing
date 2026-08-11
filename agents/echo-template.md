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

- When a human-readable refresh is useful, run the producer to generate the run-local `Generated/echo-residuals/<source_id>.md` projections on demand; they are not in the Git index. Never require writing a global aggregate file or hand-edit generated residual data.
- Residual counts, mother residual `atom_id` lists, and `unresolved-subitem` lists must never be counted, written, edited, or reordered by hand. They are projections of `digest-status --residual-summary`, which uses the same evaluation as `digest-status --json`.
- Residual projections are human-readable snapshots, not publication evidence or a freshness gate.
