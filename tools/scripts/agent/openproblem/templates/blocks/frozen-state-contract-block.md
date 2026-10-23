## Frozen ledger contract (binding; overrides every older wording in this brief)
`origin/dev` has no `Golden/Frozen/accepted/` directory. The module state records are the sole frozen registration table.
- **What the freeze doors write.** They write only `Golden/Frozen/state/<module path>.lean.json` records, `{statement_id, declarations}`. Commit no file under `Golden/Frozen/accepted/`. If your branch carries one from an earlier attempt, delete it, then rerun the door with the current tools after merging dev.
- **Wherever this brief says** "Freeze event", "event hash" or "accepted Freeze", read the module state record: its path and its module `statement_id`. The PR body reports that pair (CLAUDE.md §4.7 ③).
- **Declaration identities** come from the Lean report, not from the ledger.
- **Rebuild the tools** after merging dev (`make -C tools dotnet`). Follow the doors' current usage (`make help`) where it differs from this brief.
