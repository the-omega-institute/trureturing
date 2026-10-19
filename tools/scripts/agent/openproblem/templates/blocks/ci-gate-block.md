## No local full gate; the required CI check is the gate (binding; overrides every step of this brief that runs or reports a local full gate)

The local full gate builds a whole-library Lean report (35–45 GB, one producer per machine), so every lane on this machine waits for it in turn. CLAUDE.md §8.2 makes local checks early feedback and the remote required check the admission authority. The CI `current` job runs the same Lean report, check-current, Scribe and check-delta on the PR's merge tree.
- Skip the local full gate and name it under `not_run`. The doors still run their own scoped checks (`ledger-align`, `make deposit-uncovered`/`make deposit`, `make emit`). A `--selector` re-pin uses `make lean-report-scoped LEAN_TARGETS="<exactly the selected modules, dotted>"`.
- After the push and `make pr … DRAFT=1`, wait for the required check on the pushed head with `gh pr checks <PR> --watch` in a bounded wait.
  - If `required` fails, read the failing job's log (`gh run view <run> --log-failed`) and treat each Block diagnostic as the gate would have, under the authorized mechanical fixes. Push the fix and wait again.
  - Report `open` only for a diagnostic outside those fixes.
- The PR body's Verification section states the gate as current data: the required check `required` at the delivered head, with its run id and conclusion, and the `current` job's conclusion. It names any Observe diagnostics the job printed for this lane's paths (SL-022 on `.scribe.cs`, SL-031 DTR, SL-008 `FROZEN_PIN_CHANGE`) as non-blocking, and says that no local full gate was run because CI's `current` job runs the same checks.

**Bounded `current` job and the PR cache seed (binding).**
- The required `current` job of `ci-current.yml` has a 30-minute limit. When a delivery adds or changes enough modules, the job ends `cancelled` and its log shows `::error title=Lean cache seed required::` or `LEAN_REPORT_CACHE_MISMATCH`.
- That is a missing PR seed, not a defect of the delivery. Handle it as follows:
  1. `gh pr edit <PR> --add-label lean-cache-produce`.
  2. Wait for the `lean-cache-publish.yml` run triggered by that label (`gh run list --workflow lean-cache-publish.yml --branch <branch>`) to complete with `success`.
  3. Run `gh run rerun <the cancelled CI run id> --failed`.
  4. Wait with `make pr-watch` again on the same head.
- Push no empty commit for this, and never report the cancelled run as a content failure.
