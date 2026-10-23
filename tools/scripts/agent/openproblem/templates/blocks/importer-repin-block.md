
## Frozen importers of published owners (binding)
If the delivery removes `private` from, moves, or otherwise edits a declaration of a frozen owner, the statement identity of every frozen module importing that owner, directly or transitively, can move although its source is unchanged. CI then fails SL-008 with a pin mismatch on an untouched module.
- **Scoped report.** Before the doors, list those frozen importers (state records under `Golden/Frozen/state/`). Include them in `make lean-report-scoped LEAN_TARGETS=…`.
- **Re-pin.** Re-pin every module whose pin differs with `ledger-align --selector <module> --candidate-lean-report <scoped report>` in the same builder commit, changing no Lean source.
- **Report.** List the re-pinned importers with old and new pins.
