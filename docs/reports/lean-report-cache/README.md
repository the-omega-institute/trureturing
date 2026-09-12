# Lean report cache

`make lean-report` 生成或复用规范报告
`.lake/build/stratalint/raw-lean-report.json` 及其完整 sidecar 和 statement
materials。报告缓存与 Lean 的 `.lake/build`、`.lake/packages` 缓存分开，默认开启；缓存
只能加速，失效或不可用时仍走权威生产路径。本文描述当前接口和已测边界，不作最终 CI
资格或 dev 交付声明。

| 命令 | 用途 |
|---|---|
| `make lean-report` | 先验证并复用当前报告；没有可用条目时按普通路径生产，必要时使用兼容 seed。 |
| `make lean-report-cache-from-github` | 将兼容的共享 bundle 取入本地缓存；先接受兼容的本地 seed，再尝试远端。随后运行 `make lean-report`。 |
| `make lean-report-cache-to-github` | 发布已有的当前完整 bundle，不执行 Lean build。 |

发布其他已有报告可设置 `LEAN_REPORT=/absolute/path/report.json`（相对路径按 make
工作目录解析）。报告必须对应当前 worktree 的输入，并带齐相邻 bundle 文件；发布不会
替你重新生成报告。远端操作使用 `gh`：读取需要所选仓库的 read 权限，发布需要
contents write 权限，可用 `gh auth login` 或 `GH_TOKEN` 配置。

报告地址由[规范输入 owner](../../../tools/scripts/report/lean-report-input.sh)
按固定字节编码计算：

| 地址 | 字段 | 用途 |
|---|---|---|
| `R`（repository input） | `repository_inspector_sha256`、`lean_sources_sha256`、`lean_config_sha256` | CI Actions 报告缓存地址及 `.input.attestation`。 |
| `A`（local/provenance input） | 上述三项加 `producer_sha256` | 本地缓存目录、`.provenance.json` 及生产/复用 provenance。 |

两种地址不可互换；commit ID 和 worktree 名称不参与 key。Release 资产名携带 `R`，
兼容前缀固定 producer、inspector 和 configuration 坐标，允许 source 差异由增量生产
处理。远端 bundle 导入后按 provenance 地址 `A` 暂存。

正常路径保持完整性和语义校验：

1. exact 本地条目须由[pair producer](../../../tools/scripts/lean-report-pair.sh)
   校验报告 hash、input attestation、provenance 及完整 bundle。
2. exact miss 后，匹配 producer/inspector/configuration 的 seed 交给既有
   [delta producer](../../../tools/lean-inspector/delta.py)。
   它按当前模块 source hash 和登记的 affected cohorts（包括声明的 claim 依赖）重检，
   保留未受影响的 records 和 materials；source-stale seed 不是当前报告。
3. 没有兼容本地 seed 时，自动远端获取先尝试 exact，再尝试最新兼容 source seed；
   exact 可直接复用，seed 必须经过普通增量生产。缓存条目无效、缺失、损坏或认证/传输
   失败时回落普通生产；仓库输入登记错误与非法获取参数仍直接报错。显式的获取或发布
   目标在请求动作不能完成时返回失败。

`lean-report-inputs.json` 是 FILEMAP 登记的输入、模块、configuration 和 cohort 权威；
[selection reader](../../../tools/scripts/report/lean-report-selection.py) 消费其闭合字段
`schema_version`、`report_modules`、`inspector_sources`、`config_inputs`、
`producer_scopes`、`impact_cohorts`。路径集合是大小写敏感的仓库相对 POSIX 路径，
逐项声明 `include`（`pattern`、`optional`）和 `exclude`；必需项须匹配排除后的普通
文件，可选项才允许缺失，选择不能穿过 symlink。`producer_scopes` 登记
`lean-report` 与 `scribe-content`；只影响报告的 policy projection 进入 compatibility。
每个当前或删除的模块恰有一个 cohort owner，`depends_on` 按声明关系取反向传递闭包；
缺失、不安全、冲突或未覆盖的登记是命名的 fatal input/selection error，绝不猜测输入
或静默改为全量重检。

本地缓存根目录和控制项如下：

| 环境 | 默认根目录 |
|---|---|
| 本地 | `${XDG_CACHE_HOME:-$HOME/.cache}/stratalint-lean-report-cache` |
| `CI=true` 或 `CI=1` | `${RUNNER_TEMP:-${TMPDIR:-/tmp}}/stratalint-lean-report-cache` |

| 设置 | 作用 |
|---|---|
| `STRATALINT_REPORT_CACHE_ROOT` | 覆盖为绝对路径；须由当前 UID 拥有且 group/others 不可写，并与 Lean build/dependency store 分开。 |
| `STRATALINT_REPORT_CACHE_REMOTE=0` | 禁止普通 `make lean-report` 自动远端获取（默认 `1`）；本地复用仍可用。 |
| `STRATALINT_REPORT_CACHE_REPO` | GitHub 仓库，默认 `the-omega-institute/trureturing`。 |
| `STRATALINT_REPORT_CACHE_TRANSFER_TIMEOUT_SECONDS` | 上传/下载超时，默认 `1800`，范围 `1..86400` 的十进制整数。 |

共享 bundle 使用 Release 存储；每个 content-addressed ZIP 带 transport SHA-256 sidecar，
包含规范化 raw report、`.sha256`、`.input.attestation`、`.provenance.json` 和
`.materials.zip`，不含 process logs。[transport helper](../../../tools/scripts/report/lean-report-cache.py)
检查成员、digest、输入坐标和 ZIP 完整性，再交给既有 delta owner；transport 校验本身
不替代消费者对 statement materials 的语义接受。

CI 在其 PR/push 事件范围内按 `R` 尝试 Actions 报告缓存。经完整 bundle 和候选输入
重新验证的 exact hit 可以在 Lean toolchain restore/build 前供报告使用；prefix restore
只提供可能过时的 delta seed，不能直接作为当前报告。push 且实际生产成功时保存报告
bundle；失败、未命中或复用校验失败都回落原有生产和检查。配置的成功 push 发布 job
在 `candidate-engineering`、`lean-inspect`、`baseline-admission` 成功后，以
job-scoped `contents: write` 的 `GH_TOKEN` 发布共享 bundle，发布失败不改变必需检查；
CI 读取共享 Release 则需要 read token。`R`、`A` 和共享 Release 资产地址不包含分支名
或 commit 名称；CI 对 `integration-*` 的 Actions 报告缓存和项目构建缓存附加分支
前缀，`restore-keys` 依次尝试本分支前缀和无作用域前缀；普通 dev 使用空前缀。
前缀不改变输入地址或报告的接受条件。

`truth-release-publish` 为选定的已验 dev 源码依次尝试 Actions 精确报告、该源码的
gate 报告工件和共享 Release 精确报告。每种复用都须通过完整 bundle 和当前输入
校验；兼容旧报告只能作为 seed。没有可直接复用的当前报告时，Release 调用一次
`make lean-report`，由现有 Lean-cache ensure 和报告 producer 完成必要准备与生产，
再组装七个 truth-release 工件。缓存复用不省略七资产及其 provenance 检查。

Judge binary cache 只避免重复构建 judge 工具；restore、测试、selftest、compile-failure
proofs、报告输入寻址和报告语义检查仍各自执行。Lean cache 的
[语义输入 key/helper](../../../tools/scripts/worktree/lean-cache-input.sh)、
[ensure 与 `.lake` 管理](../../../tools/StrataLint.Cli/Commands/Worktrees/LeanCacheEnsureCommand.cs)
及[归档 writer](../../../tools/scripts/worktree/lean-cache-publish.sh)保持原有分工。

## 内存与增量边界

以下四行绑定生产源码
[`5350a3b49b90cdf4248f130b348715aaa90f1a60`](https://github.com/the-omega-institute/trureturing/commit/5350a3b49b90cdf4248f130b348715aaa90f1a60)
和全量输入一致的
[`38f8b5882b02bde354b730172ebfc1b93715b939`](https://github.com/the-omega-institute/trureturing/commit/38f8b5882b02bde354b730172ebfc1b93715b939)。
条件均为共享 Darwin M3 Ultra、96 GiB、Lean 4.33、私有 warm `.lake`、
`STRATALINT_REPORT_CACHE_REMOTE=0`，
`make lean-report` 单进程原生 RSS 观测：

| 模式 | 墙钟秒 | 最大单进程 RSS | Built | Replayed | Inspector |
|---|---:|---:|---:|---:|---:|
| 全量报告生产 | 3021.05 | 8.392868 GiB | 0 | 3403 | 4160 |
| exact 本地复用 | 77.68 | 263.171875 MiB | 0 | — | 0 |
| 源码 delta | 673.82 | 5.577148 GiB | 2 | 3402 | 16 |
| 叶模块注释 delta | 181.14 | 5.516693 GiB | 1 | 3402 | 4 |

四次运行及完整 bundle 校验均成功；exact 没有启动 producer，raw 和 materials 字节等于
全量结果。上述 RSS 是单进程最大值，不是同时运行总内存或最低 RAM，也不能外推 CI
时序。Lean `.olean` 的增量编译与报告 Inspector 是两件事：即使 `Built=0`，全量报告
仍须加载登记的依赖环境并检查 4160 个模块；exact 命中才跳过 Inspector；source delta
由既有 owner 重检受影响闭包并合成完整报告。依赖加载和保留完整 materials 使内存不会
随重检模块数线性下降，报告语义不因 `include_in_statement=false` 而丢弃必要材料。

受控 ZIP merge 对相同 materials 和 ZIP 参数的 old/new/new/old 完整生命周期耗时为
11.039/11.667/11.533/11.452 秒；RSS 由旧版 1.28–1.53 GiB 降至新版约 0.48 GiB，
输出 bytes 相等，最大 524542649-byte member 使用有界拷贝。该结果只说明合并过程的
内存边界，未证明整体加速或全程峰值下降。
