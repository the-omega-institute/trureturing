# Lean inspector

`tools/lean-inspector` 统一管理 Lean report 的生成、工件、依赖驱动的增量和发布，
完整调用复用由登记输入和成功证据校验决定；需要构建时由 Lean/Lake 的原生依赖与工件机制决定增量，没有独立报告缓存层。

在仓库根目录运行规范入口，生成或复用当前 Lean 报告：

```sh
make lean-report
make lean-report LEAN_REPORT=.lake/build/stratalint/custom-report.json
make lean-report REBUILD_REPORT_CACHE=1
```

本地默认 `fetch-or-fail`：报告种子缺失、不完整或成功收据的 `inputs.report_format`
不符时，主 checkout 先在私有写锁内恢复 dev 同分区、缓存 key 一致的 Release 快照。恢复后仍无
相符种子时，以 `LEAN_REPORT_CACHE_INCOMPATIBLE` 和非零状态退出，不进入 Lake 报告提取。
production Release 恢复（`make lean-cache-from-github-without-mathlib`）和
`fetch-or-fail` 报告恢复只在主 checkout 运行；显式选择的 verification-mode fetch 不变。
linked worktree 的 `fetch-or-fail` 在所选种子缺失、不完整、损坏或格式不符时，先检查
工作树内的 canonical 种子 `.lake/build/stratalint/raw-lean-report.json`；相符时从它复用，
发布到 `LEAN_REPORT` 指定的输出，不取回 Release。canonical 种子也不可用时，以
`reason=linked-worktree` 和退出码 4 拒绝。
补救前提是主 checkout 为干净的 `dev` 检出；否则 `warm-donor` 以退出码 0 和
`skipped` 收据返回，这不代表 donor 已预热。先在该主 checkout 同步、预热并成功生成
相符的封口报告，再移除 worktree 的 `.lake` 并由 ensure 从热主 checkout 重新播种：

```sh
make -C '<main checkout>' warm-donor && make -C '<main checkout>' lean-report && rm -rf -- '<worktree>/.lake' && make -C '<worktree>' lean-cache-ensure
```

ensure 不会用 donor 替换已有且 stamp 相符的 `.lake`，所以重新播种须先移除它。
主 checkout 可用 `make lean-cache-from-github-without-mathlib REFRESH_STALE=1`
显式取回并替换 Release 快照；无法判定 Git checkout 类型时拒绝取回。
linked worktree 只在 Git worktree 列表首条候选的物理顶层路径及共同 Git 目录均通过
核验时给出主 checkout 路径；候选为 bare、记录缺失或不可解析、核验不通过时仍拒绝，
补救要求在本仓库的 dev 主 checkout 执行 `make warm-donor && make lean-report` 后重新播种，
并说明无法从当前 worktree 确定其位置，不将 Git store 目录当作主 checkout。
格式相符而输入有差量时，干净的 dev 主 checkout 读取 `.lake/lean-report-seed-base.json` 中的生产提交，
记录的 `seed_sha256` 绑定 canonical 报告、全部四个 sidecar 和成功收据的实际字节；任一成员不符或缺失时 base 未知。已未知 base 的记录清理失败只报告维护诊断，不拒绝有效复用或阻断生产准备；实际替换 generation 的 provenance 写入与失效要求不变。
只有选中的种子是 canonical 种子时才进行可选刷新；自定义种子打印 `reason=non-canonical-seed` 并保留。
未知 base、不干净、CI、非 dev 或 detached checkout 均在列举前打印各自的 keep 收据并返回。
可继续选择时列举兼容 Release 分区的最新快照。只有快照清单的 `producer_commit_sha` 是当前 `HEAD` 的祖先、
且本地记录是它的严格祖先时才在现有缓存锁内用 `--refresh-stale` 取回；本地记录未知、快照较旧
或不在当前历史上时保留本地种子。缺失对象或浅历史无法证明祖先关系时打印 ancestry-unprovable 原因，
与完整历史上已证的非祖先区分。列举、清单读取或取回失败且回滚成功时打印 keep 收据并继续 Lake 增量路径；
输入也相符时打印 `action=keep`、`reason=seed-current`，整份收据仍可直接复用。
复用阶段完成后，入口立即打印一次决策收据，再进行 provisioning、ensure 或程序构建；后续失败保留原退出码。
可选取回只恢复已批准的 tag，并核验清单生产提交与批准值一致，
不重新列举或向较旧快照回退。替换前检查 staged 报告的格式和完整性；build 与 base 在同一安装中
提交，提交前的失败恢复原 build 和 base，提交后的备份清理失败保留备份并报告已安装。
回滚失败单独报告 `rollback-failed` 和保留的 backup 路径，以 `reason=release-rollback-failed` 非零退出；
可选刷新后重新检查种子，缺失或不兼容时拒绝进入 Lake。
干净谓词包含未跟踪文件。成功的 canonical 种子生产和验证后的恢复更新该记录，
恢复写入清单的生产提交与安装种子的完整身份；新种子没有可信 base 时先清除旧记录。
canonical publication、seal 和 base 写入在同一缓存锁内完成，seal 核对 publication 返回的五件 bundle 身份，
已被替换的 generation 不重封或改写 base。base 还绑定 seal 写入的成功收据；从 canonical 整份复用时更新身份并保留原生产提交，从自定义种子发布到 canonical 时 base 未知。
capture 只读输入，不改 base 或成功收据，也不依赖 Release 模块。canonical 生产准备只在现有缓存锁内移除 metadata。
失败清理不移除 canonical 成功收据或 base；入口未改变 canonical 报告时，包含复用后的程序构建失败，保留当前收据和 base。
成功收据仅在持有现有缓存锁、即将改变报告的准备阶段移除，并在报告成功封口后写入。
已准备的生产失败保持无收据，下一次入口按既有缺失种子恢复路径处理。锁忙时不改活动 generation。
自定义输出的生产准备和 seal 保留 canonical base。
跳过或拒绝的恢复不改 base。
CI、非 dev 和 detached checkout 不进行可选刷新。记录不参与格式、输入、收据或缓存 key 的兼容性判断。
`REBUILD_REPORT_CACHE=1` 跳过报告恢复和整份收据复用，显式允许报告构建路径；
主 checkout 的 ensure 仍可按现有主检出专用路径由归档补齐冷的项目层。
CI 与 Release publisher 显式传入 `LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build`，
跳过报告恢复；环境变量不选择本地或 CI 策略。直接 `inspect.sh` 默认 `reuse-or-build`，
也可显式传入 `--cache-miss-policy fetch-or-fail`。兼容性只由报告格式标识表达，
没有判官语义版本或旧格式适配。种子需保留报告、四个 sidecar 与 `.reuse.json`。

`LEAN_REPORT` 可省略；默认输出为
`.lake/build/stratalint/raw-lean-report.json`。相对目的路径按仓库根目录解析，
也可用绝对路径；修改目的路径只改变发布位置。需要仓库钉版的 Lean/Lake、.NET SDK
和 Python 3。[入口](inspect.sh)负责输入验证、utility 输入工具构建、Lean-cache
ensure、原生 Lake 报告构建和发布。

The native executables `reportInspector` and `compiledJudgeTests` have no D5,
Reg or Mathlib modules in their transitive Lean imports. Their static contract
dependency is the mathematical-dependency-free Core module. Mathematical
contract heads use fully qualified names; the existing `RawArtifacts` reader
loads their compiled declarations at runtime. Root `make compiled-judge-test`
delegates to [the test entrypoint](../scripts/compiled-judge-test.sh), which uses
`make lean` to build the test library and both executables, then runs the native
tests. The library's existing directory glob includes
[Fixtures/CompiledInputs.lean](LeanInformationAuditRegTests/Fixtures/CompiledInputs.lean);
its imports register the runtime Reg inputs. Lake builds these dependencies and
the fixture artifacts separately from the executable import graph; dispatchers
carry no copied Reg module list. The executable checks both compiled program
import closures and enumerates contract name literals in compiled implementation
expressions to verify each against the interface artifacts. Missing input
artifacts, unknown names and malformed structures produce named failures.

Typed contract discovery inspects the five direct compiled Contract heads.
Entries have safe, closed definition values; the decoder accepts constructor
trees and safe constant references. Standalone ExpectedDeclaration is rejected
by the root structure rule. Rigid universe checks apply to the compiled terms.

`Contract.Ref` stores only `value`. The decoder reads its compiled constant head
by stripping Expr metadata and following application functions. Lambda, let,
projection, open and unknown-constant payloads receive a field-role diagnostic;
the decoder never reduces them. Registration target identity comes from the
target constant in the contract type, with theorem, closure, arity and rigid
universe checks. `Registration.targetName` is absent.

Contract types bind the original mathematical obligations to the target, arena,
actual realization, primitive bundle and catalog indices. The Reg compiler checks
variation, slot sensitivity,
source-family obligations, seal lowering/triviality, closure membership,
retained kernel collisions and catalog conclusions. Missing, unknown, absent and
unsupported evidence remains a compilable submission and retains its diagnostic
path. The report consumes these fields and reconstructs raw ownership, enrollment,
source scope, catalog membership, ordering and joins. Checked plans, joins,
assessments, verdicts and report receipts are never importable authority.

The bounded `CompiledExpressions.sameShape` comparator uses supported semantic
equalities on compiler-checked terms; it is not a definitional-equality test.
For two `Decidable.decide` applications it compares the propositions and omits
only their decision-instance arguments: any instances for the same proposition
give propositionally equal Boolean results (`decide_eq_decide` in Lean).
Other instance and dictionary arguments remain subject to ordinary comparison.
`CompiledCalculations` tests the same-proposition/different-instance case,
different propositions and distinct `ToString` dictionaries.

Finite seal catalogs carry nondegeneracy and bundle nonemptiness for their exact
arena and unit vector. Unsealed finite registrations retain their existing scope;
they do not acquire a nondegeneracy requirement. Checked readout sensitivity
already implies nontriviality of every readout output: the law flip forces two
different readout functions at that slot, hence two different output values.
These consequences have no duplicate Registration fields.

Raw statement, arena and bundle correspondences use literal `ExactMatch.evidence`
constructors whose expected and actual type indices are identical. They retain
the original definitional correspondence; propositional equality, equality
transport and computed tokens do not supply literal matching evidence. Unknown,
absent and unsupported constructors keep arbitrary actual indices representable.

The production judge discovers typed declarations in compiler inventories. It decodes
constructor trees and constant references, independently of source syntax,
modifiers, suffixes, options, notation or metaprogramming commands. A value
requiring computation fails by name as `contract.decode_failed:<owner>:<declaration>:<reason>`,
including the field-specific `contract.literal` diagnostic. Missing compiled declarations and
unknown constructor layouts fail without a fallback.

Reg's transitive dependency closure excludes the judge implementation through
`REG-IMPLEMENTATION`. Its entries and mathematical fields are checked by the
compiler. Source text does not supply a second writing gate.

Reg module kinds come from the `Reg/Catalogs/**` subtree: its exact
`RootCatalog.lean` leaf is a catalog and `SealedCatalog.lean` is a sealed catalog.
Every other file is ordinary, including D5 mirrors with either reserved leaf
name. The loaded Reg import closure and canonical source paths construct these
obligations before entry discovery, without an instance table. Every required
source must exist; omitting a loaded Reg module from discovery receives
`contract.root_structure:required_module_missing`.

Ordinary modules contain no RootCatalog or Seal; catalog modules contain exactly
one RootCatalog and no Seal; sealed catalogs contain exactly one of each. Root
IDs equal their owning module. Missing, extra, duplicate entries and wrong root
IDs receive `contract.root_structure:*` failures. Expected/source/baseline arrays
and contributor identities retain the existing snapshot checks. Typed catalog and seal
entries belong in reserved leaves within Reg/Catalogs; D5 registration mirrors
retain their original addresses.

Typed expected occurrences come only from RootCatalog. An entry of type
`ExpectedDeclaration` always receives
`contract.root_structure:independent_expected_not_allowed`.
Its decoder and snapshot output are absent; there is no independent-expected
fallback.

The production report reads the compiler inventory and the compiled contract
values directly. Typed discovery uses the contract type heads and compiler
owner facts; source commands, declaration modifiers, suffixes, notation and
other source spelling do not participate. Catalogs and seals from D5 mirrors
use `Reg/Catalogs/D5/<D5 relative module path>/RootCatalog.lean` or
`SealedCatalog.lean`; mirrors retain their registrations at their original
paths, catalogs import those leaves, and leaves do not import catalogs. Catalog
root IDs use the catalog module and `registrationModuleName` retains the leaf
owner. Ordinary modules require neither catalog nor seal entries; reserved catalog
leaves enforce the RootCatalog and Seal cardinalities described above.

Reg sources compile to the typed contract heads. Catalogs use RootCatalog
entries and seals use Seal entries. The report accepts constructor trees and
safe constant references from the compiled values; values requiring evaluation
fail by name and have no fallback.

[CI](../../.github/workflows/ci-current.yml) 和本地数学门通过 `make lean-report`
调用同一个 `inspect.sh`。入口可独立构建 utility 输入工具,也可接收显式的
`STRATALINT_LEAN_PRODUCER_DLL`。生成的报告交给 check-current/check-delta;
这些检查器不生成报告。离线 truth/export 与 bundle 验证工具保留,不提供
自动选择 CI 来源或发布资格的链路。

输出采用 `stratalint-raw-lean-report-v3`，同一文件名后附
`.sha256`、`.input.attestation`、`.provenance.json`、`.materials.zip`。
传递报告给消费者时须保留整组文件；statement materials 与报告一起校验。
成功输出 `RAW_LEAN_REPORT path=… sha256=…`。

Inspector 的可复用工件由 [Lake facets](lakefile.lean) 管理，均在当前仓库
`.lake/build/lean-inspector/` 下：

| 路径（相对于该目录） | 用途 |
| --- | --- |
| `producer/` | 原生编译的 inspector 可执行程序及其构建产物。 |
| `modules/<Lean.Module>.zip` | 每模块报告、materials 与实际生成来源。 |
| `report.zip` | 汇总后的完整规范报告 bundle。 |
| `inputs/`、`inputs.json`、`report-format` | 当前模块输入、成员及配置坐标、报告格式标识。 |

这些是构建产物，不提交为源码。Lean-cache 发布先经同一 `make lean-report` / `inspect.sh`
入口完成登记的程序目标、原生报告及完整校验，再打包根 buildDir；不另跑一轮 `lake build`。
输入、编译或报告校验失败即发布失败，即使本轮发布地址已存在也不能绕过。
归档携带原生 Inspector 可执行文件、模块与汇总工件，以及规范报告、materials、origin 和
attestation。发布继续使用 mathlib 分区内的 run/attempt 快照及 draft 上传协议；draft
不能作为可用种子。传输失败不改变已经完成的构建与报告结论。
Lake 编译依赖 trace、utility 输入与报告格式标识决定还原后的报告复用；
验证器只查结构与工件完整性。
正常 Lean-cache 负责依赖物化和既有构建归档；
[ensure](../StrataLint.Lean/Lean/LeanCacheEnsureCommand.cs) 按 donor
规则播种当前工作树的私有 `.lake`，支持时使用 clonefile，复制后的写入与 donor 隔离。
`.lake` 不使用 symlink；[writer 入口](../scripts/worktree/lean-cache-run.sh)
以 `with-cache-writer` 持有当前 `.lake` 的写锁，覆盖 ensure 和原生 `lake build :report`。
donor 只供播种，后续编译、报告写入和损坏恢复均发生在当前工作树。

[stamp](../StrataLint.Lean/Lean/LeanWorktreePins.cs) 由 cache producer 写入，绑定
`lake-manifest.json` 中 mathlib 的 resolved revision 与 OS/架构，不证明项目工件已齐全或报告仍有效。
缺失或损坏的 stamp 不等于 pin 已变；ensure 按现有规则补齐或原地重产。
缺 stamp、项目 olean 为冷且 `.lake/build` 不存在时，也可走 donor 的 missing-build 播种路径。
报告是否可复用由编译依赖 trace、utility 输入与报告格式标识决定。正常入口在 ensure 前不创建
默认输出或日志目录，以保留新工作树的 donor 播种条件。

程序编译义务由 `inspect.sh` 的默认目标选择；直接调用可用排序后的 JSON 列表通过
`STRATALINT_LEAN_BUILD_TARGETS` 覆盖。报告、materials 与这些构建产物随项目
`.lake/build` 缓存运输，不另建报告缓存。
正常入口校验可选 `.reuse.json`：报告格式标识、登记的报告模块与配置输入的内容摘要及 Git 记录的所有者可执行位(0755 或 0644;其它权限位不参与)、显式工具/环境/平台与上轮成功调用
一致，并且报告五件套与收据逐字节相符、信封和输入坐标仍为当前时，复用报告数据。选中的程序目标仍须通过 Lake 增量编译；未选程序目标的命中不恢复 Lean 重缓存。
缺失、损坏或不匹配时，同一次 Lake 调用构建 `:report` 和选中的程序目标。生产程序（含 Lean Inspector/audit、C#、脚本、构建属性）的字节不进入该收据，判官实现或规则变化保留有效历史报告；实际构建或检查失败仍失败，缓存命中不能代替判词。未提供覆盖值的直接调用使用 Inspector 默认程序目标。
`:report` 只构建登记报告模块及实际依赖，不隐式追加包的默认目标；选中的程序目标在报告命中与未命中时均须执行。
程序构建义务独立于模块报告失效；只影响这些构建义务、未改变报告依赖的编辑，不会因此重提取无关模块报告。实际缺失或失效的模块
提取会合批以共享加载工作，失效选择仍由 Lake 决定。输出
`LEAN_INSPECTOR_WORK extracted_modules=… aggregates=…` 分别表示本次实际提取模块数
与汇总次数。输入未变且原生工件有效时，两者均为零；报告复用时仍履行选中的编译义务
并校验报告材料，current/delta 检查继续执行。编译失败返回非零并清除该输出的 `.reuse.json`。
这两个计数不表示 Lean 重编数量；进程 RSS 观测也不表示最低 RAM 要求。

[lean-report-inputs.json](../../lean-report-inputs.json) 是 FILEMAP 登记的唯一输入
清单，声明 `report_modules`、`inspector_sources`、`config_inputs`、
`producer_scopes`，并可声明 `dependency_sources` 和完整调用的 `report_execution` 环境。
首次生成 `.reuse.json` 须成功完成选中的程序目标、report 和发布；命中后核对信封并重发布报告，
同时履行选中的编译义务。该证据随 current 种子传输，不改变报告 schema、模块来源或远端 mathlib 分区。
[读取器](../scripts/report/lean-report-selection.py) 只展开显式登记的路径集合；路径为
大小写敏感的仓库相对 POSIX 路径，按 `include`（`pattern`、`optional`）及 `exclude`
选择，报告模块必须能在 Lake workspace 中解析。`dependency_sources` 与 `report_modules`
共同给出允许捕获的本地 Lean 源码范围；它是登记清单，不是另一套失效规划器。
接口契约源码登记在现有 `config_inputs`，接口变化使整份收据未命中；Lake 只重编并重评受影响的编译闭包。
仅登记为 producer、未进入模块或 utility claim 依赖闭包的文件，不会因此使报告失效。

报告复用只依赖编译输入、utility 输入与报告格式标识。判官实现或规则改变保持历史报告；新增或改动的登记经编译依赖变化交给当前判官评定。契约接口改动须同次交付迁移全部用法、删除旧路径，受影响的 Reg 自动重编并重评，不做历史兼容。需要重判未改动的历史登记时显式生成不带缓存的完整报告。

报告格式标识由 [读取器](../scripts/report/lean-report-selection.py) 的 `REPORT_FORMAT` 给出，用于 raw report schema、输入坐标、整份报告收据及所有模块 trace。声明、公理闭包、statement identity 等提取语义或工件格式改变时更新该标识；严格读取器拒读旧格式，全部模块重提取。判官实现字节不进入复用条件；当前选中程序仍须编译成功。

[原生依赖](lakefile.lean)按以下输入决定报告工作：
逐模块工件 trace 只取模块及 utility claim 的编译闭包、utility 输入与报告格式标识；inspector 程序仅等待构建成功，不额外混入其 trace 或源码绑定。
enrollment plan 不保存源文件字节摘要；plan identity 与模板 assessment 消费编译信息，导入源码的纯注释编辑不改变它们。

| 输入变化 | 失效范围 |
| --- | --- |
| 报告格式标识改变 | 全部模块报告重提取并重建汇总；旧格式严格拒读。 |
| 模块源文件、编译工件或传递 import 工件变化 | Lake 依赖 trace 对应的模块报告；模块自身源码逐字节追踪，导入模块只按编译工件追踪，注释不改变编译工件时复用导入者。 |
| 模块 utility 记录变化 | 对应模块报告；声明的 claim 源码、编译工件及其传递依赖同样参与，即使 claim 不在 result 的 import 闭包内。 |
| 登记的 `config_inputs` 文件字节变化 | 通过 Lake 影响实际编译依赖；整体配置身份只影响聚合。 |
| 登记的模块成员集合变化 | 汇总按当前集合重建，新成员执行所需报告工作，保留仍有效的模块工件。 |
| 判官实现或规则变化 | 全部有效报告复用；Reg 零重编，选中程序仍须构建成功。 |

`information_templates` 分区携带 occurrence inventory 和 BindingRecord，
其闭合字段为 `schema_version`、`inventory`、`registered`、`records`，不写全局版本；复用验证检查结构，不重算当前源码摘要。
C# 消费者检查可解码证据的结构、sidecar 归属及 debt 约束；未决记录保留具名诊断。
没有模板模块的隐式导入。独立编码测试使用显式 `--statements-only`，其结果不含
binding evidence，不能通过声明模板的严格消费者。
`LeanInformationAuditRegTests` 的生产证据检查要求实际导出的 wire 等于对应 `Compiled*Wire.canonical`，C# 测试读取同一字面量验证消费契约；该字面量是 Lean 源，由 Lake 的 import 追踪；当前 wire 只在实际内容改变时同步更新。

H 由目标自身编译常量的精确契约类型头与 owner 判定，包含 Registration、TemplateEnrollment、RootCatalog、Seal；只 import 登记的汇总模块不在 H。小型类型/owner/名字投影由 Lake 直接调用独立的 `inputDiscovery` 程序产生；它只读取目标的 olean parts，复用相同类型与字面定义检查。投影只以编译闭包追踪，不持久化评定权威。origin 保留实际生成来源和输入投影；聚合与整份收据核对当前报告格式，旧格式拒读。程序字节永不进入数据工件复用条件。

Lake 的 `transImports` 为模块及其 utility claim 选择传递源码依赖；编译工件 trace
包含 inspector 私有导入所需的传递依赖。捕获结果写入模块输入旁的 `.sources.json`，
由 [native producer](native.py) 检查本地路径均在上述登记范围内。
报告行只保留自身的 `source_path`/`source_sha256`；
导出证据和来源 sidecar 不重复存储导入源码的原始摘要。
外部包依赖由登记的 Lake manifest pin 约束。

报告格式身份与实际产地分别记录。[provenance-v4](publication.py) 的
`producer_sha256`、`repository_inspector_sha256` 承载报告格式标识的哈希；实际生成来源的摘要记在
`module_origins` 各模块的 `producer_sources_sha256` 和
`inspector_executable_sha256`，并绑定该模块报告哈希。复用保持原始来源，增量汇总可含
多个真实来源；`mode=cached` 或 `produced` 描述本次发布工作，不把旧报告改称当前
可执行文件新生成。

导出的 bundle 以 `module_origins.report_sha256` 检查来源记录与报告行的完整性。
发布和导出报告的 [输入验证](../scripts/report/lean-report-input.sh) 核对来源记录、模块成员与登记路径，
不重算当前源码、claim 源码或捕获依赖的文件摘要来决定复用。
提取语义或报告格式改变时更新报告格式标识；判官实现或规则改动保留未改动登记的既有判词。
判官实现改动不要求旧行的生成指纹等于当前 producer；重新生成的行才记录新指纹。
仓库输入地址与 provenance 的 `input_address` 由同一输入工具按各自编码计算，
不能互换，commit ID 与工作树名称不参与这些地址。

缺失的原生工件由 Lake 恢复或补建；与 olean 相同，trace 仍有效的工件原样复用，不再检查其内容。
默认输出或任一相邻 sidecar 丢失、损坏时重新运行 `make lean-report`，它从 inspector 工件重新发布，
必要时先补建；发布核对规范信封与输入坐标。

原生 Lake `--no-build`：

| 工件状态 | `--no-build` 结果 |
| --- | --- |
| 所需构建目标已就绪，报告工件 trace 有效 | 直接复用，零提取、零汇总。 |
| 工件缺失且无法由 Lake 恢复，或输入/报告格式/编译产物变化需要重建 | 非零退出，报告目标需要重建。 |

已用 `make lean-report` 准备好工具和私有 `.lake` 后，可以检查原生报告目标：

```sh
tools/scripts/worktree/lean-cache-run.sh lake -d tools/lean-inspector-reg --no-build build :report
```

该命令经同一 writer 入口运行，只检查原生目标，不发布到 `LEAN_REPORT`。
`--no-build` 限制 Lake 的重建，输入准备及可用原生工件的恢复仍会执行，
不是整个入口的只读模式。需要修复时重新运行 `make lean-report`。

[完整校验](publication.py) 保留每条声明的 `statement_id`、`type_sha256` 和规范
material 校验，`include_in_statement=false` 的声明也须有对应材料。与 olean 相同，模块报告工件只在生成时完整校验一次，
不通过即不写出；此后是否复用只由 Lake trace 决定（含本模块及其 claim 的编译产物，olean 一变对应报告即失效），
命中或从缓存恢复的工件不再校验。汇总按登记顺序拼接各行，原样搬运其已压缩的 materials；发布与收据复用只核对信封和输入坐标。

必需输入错误直接失败：清单缺失或损坏、版本缺失或非正整数、必需登记无匹配文件、
不安全或穿越 symlink 的路径、模块冲突或无法解析、无效的 utility/claim 输入均不
通过；不会猜测输入或把错误降为缓存未命中。只声明为 `optional` 的缺项可被接受。
Lean、audit、工具构建和发布失败也返回非零。阶段失败输出会指出
`LEAN_INSPECTOR_FAILED phase=… exit=…` 并打印诊断；阶段被信号中断时输出
`LEAN_INSPECTOR_INTERRUPTED phase=… exit=…`、该阶段已有输出及原生阶段观察，保留非零退出码。
ensure 成功后，各阶段诊断保存在
所选输出文件名后附的 `.logs/` 目录中。修正具名输入或构建错误后，仍使用同一
`make lean-report` 入口重试。

The interface consists of typed contract structures, inductives and sort-valued index families. Every Reg
entry has a contract type and mathematical fields checked by the Reg compiler. The report reads those compiled
fields and emits structural input evidence; it does not construct or recheck proofs. Runtime DTOs live in Impl;
no recorder or registration command runs during Reg compilation. Implementation edits rebuild no Reg modules;
report reuse depends on compiler inputs, utility inputs and the report format. Interface
edits atomically migrate every use, remove the old path and rebuild/reassess affected Reg compiler closures. Historical compatibility is not
supported. Existing representation upgrades preserving mathematical evidence and registration semantics are
outside the registration pause.

The production reader uses `RawArtifacts.Store` for every target. It reads compiler module parts and imported
constant tables without creating an Environment, initializing extensions, invoking elaboration, Meta, the type
checker or the kernel. Contract inputs are decoded from constructor trees and safe constant references in those
parts. A value that requires evaluation, a missing part, an unknown format or a read failure is a named
`contract.decode_failed:<owner>:<declaration>:<reason>` or raw-artifact failure; there is no fallback reader. Utility relationships compare
the raw types `Prop` and `Not claim` literally, without unfolding or reduction. `ArtifactAssessment` constructs target-local registration data;
`CompiledAssessment` executes template, evidence and binding gates; `CompiledSeal` checks independent snapshots,
source uniqueness, joins, qualified-name collisions, catalog membership and every finite vector element. Mathematical seal obligations are
checked during Reg compilation; the report computes no seal statistics. Companion constants are immutable report
views, never installed declarations. Computing compiled expression shapes and finite projections does not decode
an otherwise computed top-level contract input. Raw terms never execute code or acquire kernel authority.
Report reuse comes from the Lake compiler trace, utility inputs and the report format identifier.

A batch plans a fixed, import-closed base consisting of modules used by more than one target (including utility claims and enrollment imports). The planning pass retains only detached names and input flags and releases its module parts. Each target loads its remaining compiler parts into a separate store. Constant and owner indexes use Lean’s existing staged map: the shared base retains its hash table and target and companion insertions use the persistent hash stage, without copying the imported bucket array. Module positions and provenance classes are compiler-fact indexes extended in dependency order during loading; assessment contexts read those indexes directly. They contain no plans, verdicts or freshness state. After material acknowledgements and report-row flush, the target frame destroys its assessment, expression/axiom caches and row; the store drops all maps and metadata before its regions are explicitly freed in reverse order. Cross-target generated-name keys own their strings. The base remains fixed until process exit; it is reported separately by `STRATALINT_INSPECTOR_PROFILE`, along with target-region/root counts and boundary RSS. Native batch packing, aggregation and aggregate validation consume one module at a time; only membership, origin, material-address and offset indexes persist. Batch size remains 100; neither the report format nor reuse conditions include these observations. The downstream C# admission reader consumes one completed report and retains its per-module template payloads and material archive objects; it is outside the report-production target loop.

`STRATALINT_INSPECTOR_MODULE_WORK` 可指定本次调用的模块工作 JSONL，记录 `discover`、`extract` 和 `assess` 的实际模块工作；H 单独由编译输入投影确定。该观测不参与 trace、复用或准入，Lake 重放的构建日志不代表本次执行。

Seals retain compiler-checked nondegeneracy, bundle nonemptiness, lowering/triviality and semantic-closure membership, catalog redundancy and kernel-collision obligations. The judge checks that the arena, catalog and complete ordered unit vector match exactly the registrations in the import closure. Seal contracts and reports contain no counts, state partitions, primitive statistics or role buckets.

Utility refutations require the raw claim type `Prop` and the raw result type `Not claim`. The judge compares those compiled types literally, without unfolding or reduction. The utility and DTR exemption use the same selector: the unique included declaration with that final name component in the designated compiled module. Its full name supplies the exemption in every namespace, including no namespace. Other new public theorems remain subject to DTR; an ambiguous selector exempts none.

The implementation library contains the production artifact evaluator and its pure
support modules. Tests and independent analyses live in the downstream host
`tools/lean-inspector-reg`, which requires both Reg and Impl.
The production report builds no test library. CI explicitly builds the full
downstream test library and runs the native compiled judge tests.
`make compiled-judge-test` builds and runs the native tests against the same
artifact evaluator used by production, including constructor discovery, source
reconstruction, negative dependencies and catalog/seal checks. Fixed work and
depth limits remain effective on shared expression calculations. Calculation
memos retain the immutable compiled table and lexical context; cached results
retain their checked depth.
Equality transports retain their bound-variable context. Distinct rigid term
types are compared before mathematical data values are reduced.
A data recursor blocked on a neutral local is compared without computing a
closed opponent; proof irrelevance and structure eta remain outside this rejection rule.

Source identity checks reuse the compiler-checked `Registration.variation`
field only for the exact complete generic Law body. All raw dependencies and
proper subexpressions retain their identity checks.

Downstream projection tools do not issue registration verdicts. Utility refutations
compare the raw claim type `Prop` and result type `Not claim` literally; Lean checks
the theorem proof term during compilation. Aliases and expanded negations fail this literal relation.
