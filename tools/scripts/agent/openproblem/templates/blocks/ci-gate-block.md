## No local full gate; the required CI check is the gate (binding; overrides every step of this brief that runs or reports a local full gate)

The local full gate builds a whole-library Lean report (35–45 GB, one producer per machine), so every lane on this machine waits for it in turn. CLAUDE.md §8.2 makes local checks early feedback and the remote required check the admission authority. The CI `current` job runs the same Lean report, check-current, Scribe and check-delta on the PR's merge tree.
- Skip the local full gate and name it under `not_run`. The doors still run their own scoped checks (`ledger-align`, `make deposit-uncovered`/`make deposit`, `make emit`). A `--selector` re-pin uses `make lean-report-scoped LEAN_TARGETS="<exactly the selected modules, dotted>"`.
- After the push and `make pr … DRAFT=1`, wait for the required check on the pushed head with `gh pr checks <PR> --watch` in a bounded wait.
  - If `required` fails, read the failing job's log (`gh run view <run> --log-failed`) and treat each Block diagnostic as the gate would have, under the authorized mechanical fixes. Push the fix and wait again.
  - Report `open` only for a diagnostic outside those fixes.
- The PR body's Verification section states the gate as current data: the required check `required` at the delivered head, with its run id and conclusion, and the `current` job's conclusion. It names any Observe diagnostics the job printed for this lane's paths (SL-022 on `.scribe.cs`, SL-031 DTR, SL-008 `FROZEN_PIN_CHANGE`) as non-blocking, and says that no local full gate was run because CI's `current` job runs the same checks.

**PR cache recovery (binding; CLAUDE.md §8.3).**
- Diagnose the failing job from its actual log before choosing recovery. Cancellation, shutdown signals, `LEAN_REPORT_CACHE_MISMATCH`, a cache miss or exhausted compute allowance alone establishes neither a missing PR seed nor a content failure.
- Follow CLAUDE.md §8.3: fetch fresh `origin/dev` and check the PR head's ancestry first; if it lacks that baseline, preserve the original changes and follow the new-PR recovery there. Select `lean-cache-produce` only when the current build inputs, compatible seeds and actual diagnostic establish the need for independent long production.
- Reuse a successful producer or wait for an in-flight producer matching the exact PR/head/target. Follow §8.3's production, artifact-identity and adoption checks before retrying a failed CI run on the current head. Do not blind rerun or push an empty commit; cache production does not replace required checks.
