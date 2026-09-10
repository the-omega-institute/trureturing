# Lean report cache

本文描述正在 integration 验证的报告缓存候选。整体 CI 资格验证与 dev 交付仍为
**PENDING**，当前进展见[跟踪 Draft #6694](https://github.com/the-omega-institute/trureturing/pull/6694)；
验证期间该 Draft 保持 Draft 且关闭 auto-merge。
[PR #6750](https://github.com/the-omega-institute/trureturing/pull/6750) 已正常合入 integration
（merge `5f89ce2`），其 [native push run #34433813347](https://github.com/the-omega-institute/trureturing/actions/runs/34433813347)
的四个 job、Actions report/judge 保存和 Release 上传均成功。这些是已接受的历史安装
观测，不代表整体资格通过或已部署到 dev。

`make lean-report` produces or reuses the canonical report at
`.lake/build/stratalint/raw-lean-report.json`, together with its required sidecars
and statement materials. Its separate report cache is enabled by default and can
reuse bundles across local worktrees or acquire a shared GitHub Release seed.

| Command | Behavior |
|---|---|
| `make lean-report` | Reuse a current report or run ordinary report production, using a compatible seed when available. |
| `make lean-report-cache-from-github` | Acquire a compatible bundle into the report cache, accepting a compatible local seed before downloading. Run `make lean-report` afterward to obtain the current report. |
| `make lean-report-cache-to-github` | Publish the existing current bundle at `.lake/build/stratalint/raw-lean-report.json`, without a Lean build. |

To publish another existing bundle, use
`make lean-report-cache-to-github LEAN_REPORT=/absolute/path/report.json`.
Relative `LEAN_REPORT` paths are resolved by make. The report must match this
worktree's current inputs and have all adjacent bundle files; publication does
not regenerate them. Remote acquisition and publication use `gh`; authenticate
it for the selected repository, for example with `gh auth login` or `GH_TOKEN`.
Remote acquisition needs read access and publication needs contents write access.
Input addressing also uses the repository's .NET SDK and Python tooling.

Report input addresses come from the existing
[canonical input owner](https://github.com/the-omega-institute/trureturing/blob/5f89ce2af7d4b29af813640838ff43d45e5f438d/tools/scripts/report/lean-report-input.sh), which
owns both schemas and their byte encoding:

| Address namespace | Existing input schema and fields | Uses |
|---|---|---|
| Repository input `R` | `stratalint-lean-report-repository-input-v1`: `repository_inspector_sha256`, `lean_sources_sha256`, `lean_config_sha256` | Actions report cache input (`steps.lean-report-input.outputs.address`); `.input.attestation` field `repository_input_sha256`. |
| Local/provenance input `A` | `stratalint-lean-report-input-v1`: the same three fields plus `producer_sha256` | Local entry directory (bare hex); `.provenance.json` field `input_address`, `LEAN_REPORT_INPUT` receipt field `content_address`, and `LEAN_REPORT_PROVENANCE` receipt field `input_address` (each with the `sha256:` prefix). |

The coordinates cover the declared producer/inspector closure, Lean source
bytes, and Lean toolchain/manifest/lakefile configuration. Derive both addresses
through that owner; their hexadecimal values are not interchangeable, even when
`producer_sha256` and `repository_inspector_sha256` are equal. Commit IDs and
worktree names are not report input keys. Release asset names carry `R`; their
compatibility prefix binds `producer_sha256`, `repository_inspector_sha256`, and
`lean_config_sha256`, allowing source differences for incremental production.
Importing a Release bundle stages it under its provenance address `A`.

Normal report production follows these paths:

1. An exact local entry supplies the complete bundle after the
   [pair producer](https://github.com/the-omega-institute/trureturing/blob/5f89ce2af7d4b29af813640838ff43d45e5f438d/tools/scripts/lean-report-pair.sh) checks its report hash,
   input attestation, and provenance against the current tree.
2. After an exact miss, a local bundle with matching producer/inspector and
   configuration coordinates can seed the existing
   [delta producer](https://github.com/the-omega-institute/trureturing/blob/5f89ce2af7d4b29af813640838ff43d45e5f438d/tools/lean-inspector/delta.py). It compares current
   module source hashes and rechecks changes and affected dependents, including
   declared refutation-claim dependencies, while retaining unchanged records
   and materials. A source-stale seed is not a current report.
3. If no compatible local seed is found, automatic acquisition tries the shared
   Release's exact asset and then its newest compatible source seed. A fetched
   exact bundle can satisfy the report directly; a compatible seed goes through
   ordinary incremental production. Successful production stores the complete
   bundle for later reuse.

Linux 单模块增量的已接受证据为 [S1 PR #6768](https://github.com/the-omega-institute/trureturing/pull/6768)
及其 [native pull_request run #34439636556](https://github.com/the-omega-institute/trureturing/actions/runs/34439636556)。
在 GitHub `ubuntu-24.04-arm` 上使用已验证的 parent report seed，
`D5.S3.Zeros.MirrorPairIdentity` 的 delta 为 changed=1、added=0、removed=0、recheck=1。
以下计数分属两个阶段，不能合并为全局计数：

| 阶段 | Built / Replayed | Inspector | 耗时 |
|---|---:|---:|---:|
| Lean workflow build | 1 / 3217 | — | 100 s |
| Report producer | 0 / 3218 | 1 | 67 s |

producer 的采样 supervisor RSS 为 3978160 KiB（3.793869 GiB）。三门均成功：
engineering/report/admission 为 617/375/133 s（总计 622 s），七个 engineering project
共 4937 passed、0 failed、0 skipped。三个 job 均命中 exact judge cache；普通测试
529 s 是关键路径，report job 还含 project/dependency restore 74/46 s。完整 bundle
无缺失、多余或重复成员，当前 source hash 与输入、provenance 和 artifact 绑定一致。

[P0 PR #6761](https://github.com/the-omega-institute/trureturing/pull/6761) 的
[native run #34436572024](https://github.com/the-omega-institute/trureturing/actions/runs/34436572024)
中，一份故意损坏的报告被 expected-SHA 校验拒绝，**退出码为 2**。随后 full recovery
为 producer/Inspector=1/3961，local-exact 复用为 0/0；source/seed fingerprint 未变，
normal、recovery、reuse 的 raw、ZIP 和 input-attestation 字节相同，checksum basename
规范化与 reuse provenance 的 `produced`→`cached` 差异已解释。private copy 缺 DLL 的
O1 退出码为 2，Linux 缺 runtimeconfig 的 O2 退出码为 131；O3 在 missing-build-output
retry 后取得 positive TRX receipt 26 并恢复原 DLL，七项目仍全部通过。这些是
source-equivalent freshly-built/private-copy omission 探针，不声称在 exact restored
archive 内注入。P0/S1 均已关闭未合并，不计稳定资格。

同候选的 [default pull_request_target run #34439636832](https://github.com/the-omega-institute/trureturing/actions/runs/34439636832)
实际入口来自 default dev `0df1fdcb`/blob `dbd66d`，native 的 workflow 修订为
merge `M=80e78fd`/blob `e53346`。default full fallback producer 为 737 s、采样 RSS
13615216 KiB，raw SHA 与 native 相同；未独立采集 default Inspector count。
两次 cache scope、Lean seeds 和 hosts 不同，不能作受控的全流程因果比较，证据只覆盖
各自事件与权限下的行为；最终交付后的 dev 首次运行仍待观察。

复用已编译的 Lean `.olean` 与生成或复用完整 Inspector 报告是两件事。
本次全量 `make lean-report` 即使 `Built=0`，仍有 `Inspector=3961` 并占用大量内存。
精确报告命中在验证、暂存完整 bundle 后跳过 Inspector；真实源码增量由既有 delta owner
按权威重检闭包处理变更及受影响模块，保留未受影响的记录和材料，再合成完整报告。
无效增量仍回落全量。内存取决于加载的依赖环境和材料，不能按重检模块数线性推算。
[Inspector](https://github.com/the-omega-institute/trureturing/blob/5f89ce2af7d4b29af813640838ff43d45e5f438d/tools/lean-inspector/Inspector.lean) 仍保留 private、excluded、opaque
声明及所需材料，`include_in_statement=false` 不代表可以丢弃材料。
规范 statement 编码正文保持不变，仍先构造完整 String，再一次写出并检查 flush；
Lean 导入内存也仍在。
正常 make 仍需可用的 Lean/Lake，执行既有 ensure 与输入寻址（含 .NET 工具）。

2026-09-10 的最终本地观测使用源码 `d4f817e58de31da965c78ba706792fc7c603c2f9`；
普通组合后的 `d8a2369ab7201bf269eafcd333d8ed4e9c79ec9e` 保持六个变更文件哈希一致。
环境为 Mac15,14 / M3 Ultra arm64、96 GiB、28 逻辑 CPU、macOS 26.6.2，
Lean 4.33.0、Python 3.9.6、.NET SDK 10.0.400；复用原有热 `.lake`，
报告缓存使用新建的私有 `0700` 根目录，`STRATALINT_REPORT_CACHE_REMOTE=0`。
三种模式各调用一次 `make lean-report`，全部退出 0；delta 只修改获准的一个叶模块注释。

| 模式 | 墙钟秒 | 实际 Built / Inspector | 采样进程树峰值 GiB | 采样最大单进程 GiB |
|---|---:|---:|---:|---:|
| 全量生产 | 609.613798 | 0 / 3961 | 16.218857 | 15.158 |
| 本地 exact 复用 | 13.985564 | 0 / 0 | 0.313675 | 0.248 |
| 单叶注释 delta | 65.535379 | 1 / 1 | 3.425659 | 2.429 |

进程树读数是当前 make 后代的近似同步 RSS 采样，目标间隔 250 ms，full 最大间隔
1.575 s；不含观测器和其他 worker，可能漏掉短暂峰值。原生观测器通过真实子/孙进程
及实际触碰 128 MiB 分配、RSS 增量恰为 128 MiB 的校准。原生 child `getrusage`
另列，不能充当同步进程树峰值。full 的 Inspector / compact 分别耗时
371.704 / 151.020 s；delta compact 没有采到样本，其内存未知，不能记为零。
这些 RSS 读数不能推出最低 RAM 要求。

三份 bundle 的 9 次既有 canonical owner 校验全部退出 0，raw、ZIP 及每个成员字节
均与各自匹配的不可变基线一致。每份保留 3961 个模块、75316 条声明、63937 份材料
（未压缩 2617336307 字节），其中 excluded 27165、private 20920、opaque 1，
没有缺失、多余或重复成员。producer/输入地址随合法源码变更更新；本地 exact 的
provenance 为 `cached`，先前 Actions exact 服务保留原始 `produced` provenance，
二者属于不同 owner 路径的观测。

已证实的优化收益限于 ZIP 合并进程：相同完整材料和 ZIP 参数下，旧/新/新/旧的完整
合并生命周期耗时为 11.039 / 11.667 / 11.533 / 11.452 s，进程 RSS 峰值由旧版
1.28–1.53 GiB 降至新版约 0.48 GiB，输出字节一致；最大 524542649 字节成员采用
有界拷贝。两种顺序的耗时比为 1.056951 / 1.007084，未触发预登记的「两种顺序均
变慢 >20% 且 >20 ms」判据，不据此声称提速或全程内存下降。

较早 full 尝试的 make / Inspector 退出码为 2，**当时 Inspector 的退出原因仍未知**。
后续诊断观察到 ENOSPC，但不足以完整归因该次失败；其 PID 计数错误的采样已丢弃，
上表是修正并校准后的重测。原基线 full 的 `Built=21` 与本次 0
来自不同主机负载、构建/缓存、磁盘和观测条件，不能相减得出全程改善；共享磁盘读数
不作原因归属。

Rejected local entries and failed automatic acquisition fall through to ordinary
production. Missing assets, rejected transport bundles, authentication/network
failures, and transfer timeouts are cache misses on that automatic path. Cache
write failures are diagnostic; actual production, output I/O, and consumer
validation failures still fail normally. Explicit acquisition or publication
returns failure when that requested action cannot succeed.

`LEAN_REPORT_CACHE` receipts distinguish `local-exact`, `local-seed`, remote
`exact`/`seed`, miss reasons, and publication results. `LEAN_REPORT_DELTA_PLAN`
and `LEAN_REPORT_DELTA` report reuse/delta/full-fallback decisions with
changed, added, removed, and rechecked module counts.

The [cache helper](https://github.com/the-omega-institute/trureturing/blob/5f89ce2af7d4b29af813640838ff43d45e5f438d/tools/scripts/report/lean-report-cache.sh) selects these
default roots:

| Environment | Default report cache root |
|---|---|
| Local | `${XDG_CACHE_HOME:-$HOME/.cache}/stratalint-lean-report-cache` |
| `CI=true` or `CI=1` | `${RUNNER_TEMP:-${TMPDIR:-/tmp}}/stratalint-lean-report-cache` |

| Setting | Supported use |
|---|---|
| `STRATALINT_REPORT_CACHE_ROOT` | Set an absolute directory to override the root. Keep this report store separate from Lean build/dependency stores. The root must be owned by the current UID and not writable by group/others. |
| `STRATALINT_REPORT_CACHE_REMOTE=0` | Disable automatic remote acquisition for normal `make lean-report`, which defaults to `1`; local reuse continues. The explicit acquisition target still requests acquisition. |
| `STRATALINT_REPORT_CACHE_REPO` | Select the GitHub repository; default `the-omega-institute/trureturing`. |
| `STRATALINT_REPORT_CACHE_TRANSFER_TIMEOUT_SECONDS` | Per-upload/download timeout, default `1800`. Use a canonical decimal integer from `1` through `86400`. Metadata requests have a separate 30-second bound; CI job limits still apply. |

Shared storage uses the dedicated Release tag `lean-report-cache-v1`, created
with `--latest=false`. Each content-addressed ZIP has a transport SHA-256 sidecar
and contains the normalized `raw-lean-report.json` plus `.sha256`,
`.input.attestation`, `.provenance.json`, and `.materials.zip`. Process logs are
excluded from reusable bundles. The
[transport helper](https://github.com/the-omega-institute/trureturing/blob/5f89ce2af7d4b29af813640838ff43d45e5f438d/tools/scripts/report/lean-report-cache.py)
checks archive membership, digests, input coordinates, and ZIP integrity, and
delegates report parsing to the existing delta owner. Report schema and semantic
acceptance remain with the existing consumers. Transport validation alone does
not prove that the materials semantically cover every report declaration.

In [CI](https://github.com/the-omega-institute/trureturing/blob/5f89ce2af7d4b29af813640838ff43d45e5f438d/.github/workflows/ci.yml), runs within the configured PR and push
scope try the Actions report cache keyed by repository input `R`. A
validated exact hit serves the report before Lean toolchain restoration and
the Lean build. A prefix restore is only a possible delta seed. The ordinary
production step explicitly uses
`$RUNNER_TEMP/canonical-lean-report-delta-cache`, stages the Actions bundle there,
and enables optional Release fallback with `STRATALINT_REPORT_CACHE_REMOTE=1`
and a read token. CI can still build Lean before this pair-level Release fetch.
Normal `make lean-report` also requires an available `lake` executable and runs
the existing Lean cache ensure before staging its report.

The judge binary cache has a separate role. In `lean-inspect`, the step
`Build candidate tools before Lean report production` runs only when
`steps.judge-cache.outputs.cache-hit != 'true'`: an exact judge binary hit skips
that redundant tools build. In `candidate-engineering`, `stage-judge` requires
`steps.build-candidate.outcome == 'success'` as well as the existing push event
and ref scope. Its save still requires both a successful build and successful
staging within that scope.

These guards retain the existing locked restores, engineering test harness,
selftest, and compile-failure proofs under their normal step conditions and
failure behavior. The engineering solution restore remains guarded by
`github.event_name != 'schedule'`. A judge binary hit does not imply zero .NET
invocations: restore, test execution, selftest, compile-failure proofs, and report
input addressing still have their own work.

The optional `publish-lean-report-cache` job runs only within its configured push
scope after `candidate-engineering`, `lean-inspect`, and `baseline-admission`
succeed. It checks out that producer commit, downloads its report artifact, and calls the
publication make target with `GH_TOKEN` and job-scoped `contents: write`.
`continue-on-error: true` keeps publication failure outside the required checks.
The Actions report save retains its existing push scope and success conditions.

The report cache cooperates through existing make and producer entry points;
Lean cache keys/helpers, `.lake/build` and `.lake/packages` ownership, ensure,
and writer behavior remain separate. See
[Lean cache ownership](../lean-cache-ownership.md) for those boundaries, including
the existing CI Lean restore-action failure gap and the unverified mathlib
regeneration caveat.
