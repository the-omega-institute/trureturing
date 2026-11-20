## No local full gate; the required CI check is the gate (binding; overrides every step of this brief that runs or reports a local full gate)

The local full gate builds a whole-library Lean report (35–45 GB, one producer per machine), so every lane on this machine waits for it in turn. CLAUDE.md §8.2 makes local checks early feedback and the remote required check the admission authority. The PR checks affected Lean targets and Scribe inputs on its merge tree. Protected push CI runs the full report and applicable tree-wide checks.
- Skip the local full gate and name it under `not_run`. The doors still run their own scoped checks (`ledger-align`, `make deposit-uncovered`/`make deposit`, `make emit`). A `--selector` re-pin uses `make lean-report-scoped LEAN_TARGETS="<exactly the selected modules, dotted>"`.
- After the push and `make pr … DRAFT=1`, wait for the required check on the pushed head with `make pr-watch PR=<number> HEAD_SHA=<full-commit-sha>` once per PR and head.
  - If `required` fails, read the failing job's log (`gh run view <run> --log-failed`) and treat each Block diagnostic as the gate would have, under the authorized mechanical fixes. Push the fix and wait again.
  - Report `open` only for a diagnostic outside those fixes.
- The PR body's Verification section states the gate as current data: the required check `required` at the delivered head, with its run id and conclusion, and the `current` job's conclusion. It names any Observe diagnostics the job printed for this lane's paths (SL-022 on `.scribe.cs`, SL-031 DTR, SL-008 `FROZEN_PIN_CHANGE`) as non-blocking. Record the PR's scoped validation and the local full gate under their actual execution status.

**PR cache recovery (CLAUDE.md §8.3).** PRs restore caches read-only and compile affected targets. A protected push builds the complete report and publishes the validated project cache.
