# Lean cache ownership

The cache is an optional accelerator. Lake remains the correctness path; cache age,
coverage, or availability never enters admission.

| Mechanism | Layer and owner | Boundary |
|---|---|---|
| `make warm-donor` | Machine freshness; the machine owner may schedule it locally | Runs only on a clean `dev` checkout, pulls `origin dev`, then delegates to `make lean`. The repository installs no timer and no required path calls it. |
| Donor selection and clone | Worktree provisioning; `LeanCacheEnsureCommand` | Reads another tree under the donor guard and requires matching pin identity plus the existing donor criteria. It never updates or builds the donor. |
| Target `.lake` writer guard | Worktree mutation; `LeanCacheEnsureCommand` | Serializes writers to the target cache. It is the mutex; process probes are not locks. |
| Dependency retrieval | Dependency supply; mathlib's `lake exe cache get` and Lake | Ensuring may fetch dependencies and reports missing mathlib oleans. Missing files do not block or trigger machine-level cache cleanup; Lake rebuilds what depHash requires. |
| Repository content build | Content correctness; Lake | `lake build` owns dependency hashes and incremental repair. Donor content may be merely recent; no absolute completeness or freshness invariant is imposed. |
| GitHub archive without mathlib | Explicit content transport; repository owner | `make lean-cache-{to,from}-github-without-mathlib` remains manual. It is not called by ensure, worktree creation, admission, or required checks and has no local download cache. |
| Lean report cache | Report reuse; the opt-in caller via `STRATALINT_REPORT_CACHE_ROOT` | Content-addressed and local only. It does not supply `.lake`, select donors, or participate in admission trust. |
