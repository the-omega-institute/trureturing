# Lean inspector

`tools/lean-inspector` 统一管理 Lean report 的生成、工件、依赖驱动的增量和发布，
完整调用复用由登记输入和成功证据校验决定；需要构建时由 Lean/Lake 的原生依赖与工件机制决定增量，没有独立报告缓存层。

在仓库根目录运行规范入口，生成或复用当前 Lean 报告：

```sh
make lean-report
make lean-report LEAN_REPORT=.lake/build/stratalint/custom-report.json
```

`LEAN_REPORT` 可省略；默认输出为
`.lake/build/stratalint/raw-lean-report.json`。相对目的路径按仓库根目录解析，
也可用绝对路径；修改目的路径只改变发布位置。需要仓库钉版的 Lean/Lake、.NET SDK
和 Python 3。[入口](inspect.sh)负责输入验证、utility 输入工具构建、Lean-cache
ensure、原生 Lake 报告构建和发布。

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
variation, slot sensitivity, witness positive/constantTrue negative claims,
source-family obligations, seal counts, row classifications, closure membership,
retained kernel collisions and catalog conclusions. Missing, unknown, absent and
unsupported evidence remains a compilable submission and retains its diagnostic
path. The report consumes these fields and reconstructs raw ownership, enrollment,
source scope, catalog membership, ordering and joins. Checked plans, joins,
assessments, verdicts and report receipts are never importable authority.

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
owner. Catalogs and seals are optional analysis groups: report evaluation does
not require catalog membership, and missing seals remain named absent inputs.

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
| `inputs/`、`inputs.json`、`compatibility` | 从登记输入生成的模块输入、成员集合及兼容标识。 |

这些是构建产物，不提交为源码。Lean-cache 发布先经同一 `make lean-report` / `inspect.sh`
入口完成登记的程序目标、原生报告及完整校验，再打包根 buildDir；不另跑一轮 `lake build`。
输入、编译或报告校验失败即发布失败，即使本轮发布地址已存在也不能绕过。
归档携带原生 Inspector 可执行文件、模块与汇总工件，以及规范报告、materials、origin 和
attestation。发布继续使用 mathlib 分区内的 run/attempt 快照及 draft 上传协议；draft
不能作为可用种子。传输失败不改变已经完成的构建与报告结论。
旧两段或三段哈希的 `lean-cache-v1` 归档都只作为同 mathlib/平台的增量种子，消费时核对
manifest 与 tag 的声明地址；不恢复 config/exact/same-toolchain 选择。Lake trace 与
编译依赖 trace、utility 输入与报告格式标识决定还原后的报告复用；验证器只查结构与工件完整性。
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
正常入口校验可选 `.reuse.json`：报告格式标识、登记的报告模块与配置输入及其 mode、显式工具/环境/平台与上轮成功调用
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

报告复用不含判官语义版本。判官实现或规则改变保持历史报告；新增或改动的登记经编译依赖变化交给当前判官评定。契约接口改动须同次交付迁移全部用法、删除旧路径，受影响的 Reg 自动重编并重评，不做历史兼容。需要重判未改动的历史登记时显式生成不带缓存的完整报告。

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

兼容身份与实际产地分别记录。[provenance-v4](publication.py) 的
`producer_sha256`、`repository_inspector_sha256` 承载报告格式标识的哈希；实际生成来源的摘要记在
`module_origins` 各模块的 `producer_sources_sha256` 和
`inspector_executable_sha256`，并绑定该模块报告哈希。复用保持原始来源，增量汇总可含
多个真实来源；`mode=cached` 或 `produced` 描述本次发布工作，不把旧报告改称当前
可执行文件新生成。

导出的 bundle 以 `module_origins.report_sha256` 检查来源记录与报告行的完整性。
发布和导出报告的 [输入验证](../scripts/report/lean-report-input.sh) 核对来源记录、模块成员与登记路径，
不重算当前源码、claim 源码或捕获依赖的文件摘要来决定复用。
提取语义或报告格式改变时更新报告格式标识；判官实现或规则改动保留未改动登记的既有判词。
兼容 producer 改动不要求旧行的生成指纹等于当前 producer；重新生成的行才记录新指纹。
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
tools/scripts/worktree/lean-cache-run.sh lake --no-build build :report
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
`LEAN_INSPECTOR_FAILED phase=… exit=…` 并打印诊断；ensure 成功后，各阶段诊断保存在
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
`contract.decode_failed:<owner>:<declaration>:<reason>` or raw-artifact failure; there is no fallback reader. Utility relationships retain
their bounded computation over compiled terms. `ArtifactAssessment` constructs target-local registration data;
`CompiledAssessment` executes template, evidence and binding gates; `CompiledSeal` checks independent snapshots,
source uniqueness, joins, qualified-name collisions, catalog membership and every finite vector element, then
reads compiler-checked row conclusions and computes output statistics. Companion constants are immutable report
views, never installed declarations. Computing compiled expression shapes and finite projections does not decode
an otherwise computed top-level contract input. Raw terms never execute code or acquire kernel authority.
Report reuse comes from the Lake compiler trace, utility inputs and the report format identifier.

`STRATALINT_INSPECTOR_MODULE_WORK` 可指定本次调用的模块工作 JSONL，记录 `discover`、`extract` 和 `assess` 的实际模块工作；H 单独由编译输入投影确定。该观测不参与 trace、复用或准入，Lake 重放的构建日志不代表本次执行。

The implementation library contains the production artifact evaluator and its pure
support modules. Tests and independent analyses live in the downstream Reg host.
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

`make census` projects production registration records without reassessment.
Independent structural graph and certificate tools do not issue registration
verdicts. Utility refutations compare compiled types by bounded structural
computation; Lean checks theorem proof terms during compilation. Unsupported
comparisons fail by name.
