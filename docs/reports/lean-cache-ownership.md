# Lean cache ownership

The target policy is that cache is an optional accelerator and Lake remains the
correctness path. The local worktree cache, scheduled archive, explicit archive
consumer, and candidate report cache keep cache availability outside required admission.

下文 report cache 与 judge binary cache 的 integration 安装已有
[PR #6750](https://github.com/the-omega-institute/trureturing/pull/6750) 和
[native push run #34433813347](https://github.com/the-omega-institute/trureturing/actions/runs/34433813347)
的成功观测。整体 CI 资格验证与 dev 交付仍为 **PENDING**；当前进展见
[跟踪 Draft #6694](https://github.com/the-omega-institute/trureturing/pull/6694)，验证期间保持
Draft 且关闭 auto-merge。这些历史安装观测不代表已部署到 dev。

**Known gap:** the two CI Lean artifact restore actions, `lake-deps-cache` and
`lake-build-cache`, run inside the required `lean-inspect` job when report reuse
has not succeeded. A nonzero action result currently blocks that check. Cache
misses fall through, but restore action failures do not. This does not yet meet
the accelerator-not-gate target and is tracked separately; report reuse and the
judge binary guards do not repair it.

| Mechanism | Layer and owner | Boundary |
|---|---|---|
| `make warm-donor` | Machine freshness; the machine owner may schedule it locally | Runs only on a clean `dev` checkout, pulls `origin dev`, then delegates to `make lean`. The repository installs no timer and no required path calls it. |
| Donor selection and clone | Worktree provisioning; `LeanCacheEnsureCommand` | Reads another tree under the donor guard and requires matching pin identity plus the existing donor criteria. It never updates or builds the donor. |
| Target `.lake` writer guard | Worktree mutation; `LeanCacheEnsureCommand` | Serializes writers to the target cache. It is the mutex; process probes are not locks. |
| Dependency retrieval | Dependency layer; mathlib's `lake exe cache get` and Lake | A cache-get nonzero result or thrown exception is a warning for the wrapped `lake build`, which continues under the same target writer guard. Symlink refusal, a busy guard, and damaged target state remain blocking correctness boundaries. |
| Repository content build | Content correctness; Lake | `lake build` owns dependency hashes and incremental repair. Donor content may be merely recent; no absolute completeness or freshness invariant is imposed. |
| Scheduled GitHub archive producer | Content layer; repository owner via `.github/workflows/lean-cache-publish.yml` | Runs at `cron: '0 */6 * * *'` and publishes an archive without mathlib. It is not required; failure blocks only that publication run, while consumers retain donor/local-build fallback. Its isolated `candidate/.lake` neither reads a worktree donor nor owns a local target writer guard. |
| Manual GitHub archive consumer | Content layer; the explicit caller via `make lean-cache-from-github-without-mathlib` | Not required and not called by ensure, worktree creation, admission, or required checks. Failure is blocking only for that explicit fail-closed invocation. It writes only the caller's tree and does not select, update, or build a donor. |
| CI Lean dependency cache | Dependency layer; the `lean-inspect` job owns the `actions/cache` restore/save wiring, while Lake/mathlib own the bytes | A cache hit is not required, although `lean-inspect` is required: a miss falls through to normal production. Saves are best-effort (`continue-on-error: true`); a nonzero restore action is blocking under the current workflow. This dependency-addressed `.lake/packages` layer (`steps.lean-input.outputs.dependency_sha256`) is separate from `.lake/build`, runs only in the ephemeral `candidate` checkout, and never selects a donor or acquires the local writer guard. |
| CI Lean build cache | Content layer; the `lean-inspect` job owns the `actions/cache` restore/save wiring, while Lake owns the bytes | A cache hit is not required, although `lean-inspect` is required: a miss falls through to `lake build`. Saves are best-effort (`continue-on-error: true`); a nonzero restore action is blocking under the current workflow. This config-and-source-addressed `.lake/build` layer excludes dependency packages and never reads or writes another worktree. |
| Lean report cache | Report reuse; `make lean-report`, explicit report cache targets, and CI | Actions uses repository input `R`; the local store and provenance use input `A`. Both come from the canonical report input owner and have distinct schemas and non-interchangeable hex values. Normal production enables a UID-owned local store and optional shared Release acquisition. Existing validation and the delta producer control reuse; report storage is separate from Lean build/dependency stores, donor selection, ensure, and writer ownership. See the [Lean report cache usage guide](lean-report-cache/README.md). |
| CI judge binary cache | Candidate tools; `candidate-engineering` and `lean-inspect` | An exact judge binary hit skips the redundant report-job tools build. Engineering staging requires `build-candidate` success within the existing push scope, and saving also requires staging success. Locked restores, test execution, selftest, and compile-failure proofs retain their existing conditions. |

Lean `.olean` 复用由 Lake 负责，不能替代 Inspector 报告生产。报告增量由既有
delta owner 按权威重检闭包合成完整 bundle，保留 private、excluded、opaque 声明
及所需材料。已接受的 Linux P0/S1 探针覆盖了一次损坏报告的 expected-SHA 拒绝
（**退出码为 2**）、恢复/复用和单模块增量；两者均关闭未合并，不计稳定资格。
Lean workflow 与 report producer 的计数分属不同阶段，详细结果、内存与 ZIP 优化
的测量边界及公开 run 证据见上方用法指南。

`ASSUMED-UNVERIFIED`: no repository test proves that, at the current pin, Lake
regenerates a missing required mathlib olean without a correctness error. The writer
tests use a fake runner that returns success without creating an olean. Proving the
claim requires an isolated real-Lake integration test that deletes one required
mathlib olean and demonstrates that `lake build` regenerates it. That integration
evidence remains unverified.
