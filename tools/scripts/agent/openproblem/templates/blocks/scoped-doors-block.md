## Report kinds at the freeze doors (binding; overrides every step of this brief that names a report for `ledger-align`)

`ledger-align` reads a **scoped** report for every call that selects modules (`DagLedgerAlignWriter.AlignFromReport`: the union of `--selector` and `--add` goes through `BuildTruthScoped`).
- **What the report must be.** Its module set must be exactly the import closure of the selected modules. A full report is rejected (`Lean report schema must be stratalint-scoped-lean-report-v1`), and so is a scoped report with any extra module (`Raw Lean report contains unknown module …`).
- **Supporting freezes (`--add`) and owner or in-branch re-pins (`--selector`).** Run `make lean-report-scoped LEAN_TARGETS="<exactly the selected modules, dotted>"` EXIT=0, then `dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- ledger-align --selector <X>.lean … --add <M>.lean … --candidate-lean-report .lake/build/stratalint/scoped-lean-report.json`.
  - One call may carry both kinds when the scoped report covers exactly all its selected modules; separate calls are also fine.
  - Never include the settling module in these `LEAN_TARGETS` unless it is itself selected.
- **Deposit builds its own report.** `make deposit-uncovered` and `make deposit` build their own scoped report; run no report before them. The one-command door is `git fetch origin dev && git merge --no-edit origin/dev && git merge-base --is-ancestor origin/dev HEAD && make deposit-uncovered GID=<gid> BASE="$(git rev-parse origin/dev^{commit})"`.
- **Order and staleness.** Re-pins first, then the supporting freezes, then the commit of `Golden/**`, then the deposit door. Regenerate the scoped report a call needs after every merge or edit.
- **Whole-library operations.** Skip operations that cannot select modules and name them under `not_run`; `make emit` needs no full report.
- **A door rejects with a report-scope diagnostic not covered here.** Stop with `open`, quoting it, and change nothing under `Golden/**`.
