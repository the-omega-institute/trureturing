# 历史兼容项清单

审计基线为主仓 `dev` 的 `3c1b20c5bb0cfc0feaa4cc82c126a2131a8463c7`。仓库约定在迁移时清理旧入口、旧格式双读和弃用存根。下文逐项列出仓内调用、替代入口及清理会影响的行为。调用数按该版本的静态源码统计，仓外脚本、手动调用频率和线上缓存命中率未知。涉及 `tools/` 的结论核对了主仓锁定的工具版本 `e0a52a374ca2`。[仓库约定 §4.2](../../CLAUDE.md#L303) · [工具版本](../../Meta/tools-release.json)

## 优先清理候选

| 项目 | 留下来的行为 | 清理范围 |
| --- | --- | --- |
| 旧发布入口 `lean-cache-publish.yml` | 仅能手动触发，启动一个 runner 打印迁移提示。现行 `Cache Release Publish` 承接定时和手动发布。 | 可先退掉提示入口及 CI 路径过滤项。旧 seed 校验还用该路径识别历史发布者，移除工作流文件与修改历史来源校验是两个动作。[旧入口](../../.github/workflows/lean-cache-publish.yml#L3) · [现行入口](../../.github/workflows/cache-release-publish.yml#L3) · [历史来源校验](../../.github/actions/lean-cache-shards/legacy-seed.mjs#L55) |
| 旧生产器 `lean-cache-produce` | 411 行 composite action，包含恢复、保存、续跑及回退。旧工作流曾直接调用它，当前主仓的 workflow 和 composite action 有 0 个 `uses:` 调用。发布验证仍把文件名列为变更触发条件。 | 可连同触发条件及 FILEMAP 登记清理。现行发布由 `module-plan`、`module-worker`、`module-finish` 完成。多个入口共用的 `lean-cache-shards` 仍有调用。[旧生产器](../../.github/actions/lean-cache-produce/action.yml) · [验证过滤项](../../.github/workflows/ci-publication-verify.yml#L135) · [现行发布流程](../../.github/workflows/cache-release-publish.yml#L81) |
| 一次性 seed 迁移命令 `latest-seed`、`restore-seed`、`migrate-seed` | 从旧生产器查找或读取已固定的 seed，选择可复用的分片并迁移。三个命令都仍可从 JS 入口分派，当前主仓工作流没有调用。测试仍显式执行 `latest-seed` 和 `migrate-seed`。 | 三个命令、旧 seed 的 JS/Python 实现和专属测试可一起评估。生产计划读取旧编译检查点走下表所列的另一条路径。[命令分派](../../.github/actions/lean-cache-shards/run.mjs#L651) · [分片选择](../../.github/actions/lean-cache-shards/legacy-seed-selection.py#L11) · [测试](../../.github/actions/lean-cache-shards/test-generation.mjs#L178) |
| Hardin 递推定理的旧拼写 | 局部 notation 把 `HardinA233259PairTransfer.recurrence` 转到 `HardinA233259PairTransferRecurrence.recurrence`。只有同一证明的一个位置使用旧拼写，同文件另一处已直接使用新名。 | 可把单个调用改成实际声明名，再去掉局部 notation。验证范围是该冻结模块的定向编译和陈述身份。[直接调用](../../D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.lean#L274) · [别名和调用](../../D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.lean#L277) |

## 清理会影响现有入口的项目

| 项目 | 现有调用和退出条件 |
| --- | --- |
| 分片缓存 `legacy_prefix` | 读取器先查当前索引，再查旧前缀，并用命中的前缀取 payload。钉版工具由同一 identity 推导 v2、v1 两套地址。Truth Release 仍调用 `restore`，普通 CI 已调用 `restore-published`。退出前要覆盖 Truth Release 和发布验证的恢复路径。[双读](../../.github/actions/lean-cache-shards/run.mjs#L182) · [Truth Release](../../.github/workflows/truth-release-publish.yml#L69) · [普通 CI](../../.github/workflows/ci-current.yml#L306) |
| 整项目缓存归档和 `legacy` 模式 | 手动发布验证仍允许选 `legacy`。自动路径命中旧项目归档时也会输出 `seed=legacy`，恢复 action 用 `project_key` 下载归档。退出涉及手动选项、自动路由和归档恢复三处。[手动选项](../../.github/workflows/ci-publication-verify.yml#L9) · [自动路由](../../.github/workflows/ci-lean-release-compile.yml#L144) · [归档恢复](../../.github/actions/lean-cache-release-seed/action.yml#L79) |
| 旧编译检查点 `--legacy-checkpoints` | 生产发布的 `module-plan` 每次都传此参数。钉版 `tools/scripts/worktree/lean_module_cache.py` 在缺少基准索引时才调用 `legacy_compiler_inputs`。移除会改变首次发布或基准缺失时的冷构建行为。[生产调用](../../.github/workflows/cache-release-publish.yml#L81) · [传参位置](../../.github/actions/lean-cache-shards/run.mjs#L424) |
| 历史源码的发布能力探测 | 可复用编译工作流接收 `source`，按旧检出是否有编译 action、准备脚本及匹配的 tools pin 来启用后续步骤。主仓内两个调用点都传 `github.sha`。若退掉历史源码支持，需核对仓外的 `workflow_call` 调用方。[能力探测](../../.github/workflows/ci-lean-release-compile.yml#L63) · [两个调用点](../../.github/workflows/ci-publication-verify.yml#L44) |
| 工具锁的可选字段 `workflow_sha` | 当前锁无此字段，安装器仍接受它，旧锁测试覆盖该格式。钉版工具的 `CiWorkflowDocument.ResolveCalledGate` 用它核对旧式跨仓工作流引用。清理应同时覆盖主仓解析器和工具仓消费者。稳定 release 和已合入工具分支的 preview 仍是贡献指南支持的来源。[解析器](../../.github/scripts/install-tools.py#L65) · [兼容测试](../../.github/scripts/test-install-tools.py#L129) · [现行来源约定](../CONTRIBUTING.md#L23) |
| `make worktree-return` | 与 `make worktree-stale` 执行同一个 `worktree stale` 命令，并接受同一可选路径。规范仍列出两个名字，钉版工具的 `stale_lifecycle_cases.py` 同时测试两者。合并入口需要同步规范和工具测试。[Makefile](../../Makefile#L160) · [规范](spec/golden-ledger-repo-spec.md#L388) |
| 超立方体的两个 `private alias Legacy.*` | `adjacent_exists_flip` 和 `flip_injective` 都已有公开定理。按 `open private … from` 的来源模块及短名匹配，D5/Reg 分别有 **41** 和 **4** 个文件使用旧查找方式。先迁调用方，再移除别名。[adjacent_exists_flip](../../D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth.lean#L263) · [flip_injective](../../D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary.lean#L51) |
| 三个进入冻结清单的公开兼容名 | `SystemWidePositive` 指向 `SystemCatalogIrredundant`，同文件等价定理引用旧名。`AdmissibleIntegerTuple` 指向 `DirectTupleAdmissible`，出现在 `DHL40Two` 的定义中。`layerGapPhase` 转发给 `primeStepPhase`，出现在多个定理陈述中。三个名字都已列入各自模块的冻结状态片，改名涉及公开陈述和冻结记录。[目录判定](../../D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.lean#L350) · [素数间隙契约](../../D5/S3/PrimeGaps/PrimeGap186SourceContract.lean#L30) · [相位接口](../../D5/S3/Analytic/GoldenEulerGapWordConstraints.lean#L24) |

## 有现行用途的兼容机制

- `Reg/Support/Legacy*` 有 16 个 Lean 文件，`Reg/D5` 有 23 个文件直接导入这组模块。规范 A5.3 仍要求已有有限 catalog 在原定理和 arena 上给出桥接证据。直接清理会影响现有登记。[规范](spec/golden-ledger-repo-spec.md#L161) · [登记实例](../../Reg/D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange/InformationRoot.lean#L83)
- `RewThreeCompat` 有 9 个冻结声明，为带 `?`、`₂` 等名字提供可寻址的 ASCII 入口，也含 `@[simp]` 引理。它的 Blueprint 明示了 GID 用途。评估清理需要验证选择器和自动化证明行为。[声明](../../D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.lean#L14) · [Blueprint](../../Blueprint/D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.scribe.cs#L8) · [冻结清单](../../Golden/Frozen/state/D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.lean.json)
- `set_option backward.*` 在 D5、Reg、src、strict 共 2,099 个 Lean 文件中出现在行首（含缩进）。这些是逐个作用域调整的 elaborator 选项，删除必要性需要逐模块编译判断。OmegaChecks 也专门检查传统 importer 能否展开隐藏实现。[选项实例](../../D5/S3/HomologicalAlgebra/Solid/ProjectiveHomCompatibility.lean#L15) · [importer 检查](../../src/OmegaChecks/Interface.lean#L104)
