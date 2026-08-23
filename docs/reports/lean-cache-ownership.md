# Lean cache ownership

The target policy is that cache is an optional accelerator and Lake remains the
correctness path. The local worktree cache, scheduled archive, explicit archive
consumer, and report cache already keep cache availability outside required admission.

**Known gap:** the two CI cache restore actions run inside the required `lean-inspect`
job and a nonzero action result currently blocks that check. Cache misses fall through,
but restore action failures do not. This does not yet meet the accelerator-not-gate
target and is tracked separately.

| Mechanism | Layer and owner | Boundary |
|---|---|---|
| `make warm-donor` | Machine freshness; the machine owner may schedule it locally | Runs only on a clean `dev` checkout, pulls `origin dev`, then delegates to `make lean`. The repository installs no timer and no required path calls it. |
| Donor selection and clone | Worktree provisioning; `LeanCacheEnsureCommand` | Reads another tree under the donor guard and requires matching pin identity plus the existing donor criteria. It never updates or builds the donor. |
| Target `.lake` writer guard | Worktree mutation; `LeanCacheEnsureCommand` | Serializes writers to the target cache. It is the mutex; process probes are not locks. |
| Dependency retrieval | Dependency layer; mathlib's `lake exe cache get` and Lake | A cache-get nonzero result or thrown exception is a warning for the wrapped `lake build`, which continues under the same target writer guard. Symlink refusal, a busy guard, and damaged target state remain blocking correctness boundaries. |
| Repository content build | Content correctness; Lake | `lake build` owns dependency hashes and incremental repair. Donor content may be merely recent; no absolute completeness or freshness invariant is imposed. |
| Scheduled GitHub archive producer | Content layer; repository owner via `.github/workflows/lean-cache-publish.yml` | Runs at `cron: '0 */6 * * *'` (or manual dispatch) and publishes an archive without mathlib. It is not required; failure blocks only that publication run, while consumers retain donor/local-build fallback. Its isolated `candidate/.lake` neither reads a worktree donor nor owns a local target writer guard. |
| Manual GitHub archive consumer | Content layer; the explicit caller via `make lean-cache-from-github-without-mathlib` | Not required and not called by ensure, worktree creation, admission, or required checks. Failure is blocking only for that explicit fail-closed invocation. It writes only the caller's tree and does not select, update, or build a donor. |
| CI Lean dependency cache | Dependency layer; the `lean-inspect` job owns the `actions/cache` restore/save wiring, while Lake/mathlib own the bytes | A cache hit is not required, although `lean-inspect` is required: a miss falls through to normal production. Saves are best-effort (`continue-on-error: true`); a nonzero restore action is blocking under the current workflow. This config-addressed `.lake/packages` layer is separate from `.lake/build`, runs only in the ephemeral `candidate` checkout, and never selects a donor or acquires the local writer guard. |
| CI Lean build cache | Content layer; the `lean-inspect` job owns the `actions/cache` restore/save wiring, while Lake owns the bytes | A cache hit is not required, although `lean-inspect` is required: a miss falls through to `lake build`. Saves are best-effort (`continue-on-error: true`); a nonzero restore action is blocking under the current workflow. This config-and-source-addressed `.lake/build` layer excludes dependency packages and never reads or writes another worktree. |
| Lean report cache | Report reuse; the opt-in caller via `STRATALINT_REPORT_CACHE_ROOT` | Content-addressed and local only. It does not supply `.lake`, select donors, or participate in admission trust. |

`ASSUMED-UNVERIFIED`: no repository test proves that, at the current pin, Lake
regenerates a missing required mathlib olean without a correctness error. The writer
tests use a fake runner that returns success without creating an olean. Proving the
claim requires an isolated real-Lake integration test that deletes one required
mathlib olean and demonstrates that `lake build` regenerates it; this change does not
add that expensive integration test.
