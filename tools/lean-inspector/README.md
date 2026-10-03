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

Typed contract discovery inspects the five direct Contract heads. Admitted entries
are safe, closed `def` declarations with a structure literal body; standalone
ExpectedDeclaration is rejected by the root structure rule. Rigid universes remain
unchanged. Parentheses around the result head are accepted. Term parameters and
used section variables cannot supply a closed entry.

Metadata uses the following closed grammar. Mathematical payload fields keep
ordinary Lean elaboration; metadata never unfolds user definitions or evaluates
user code.

| Metadata shape | Accepted source forms | Compiled forms |
| --- | --- | --- |
| Name | quoted names; `Lean.Name.anonymous`, `str`, `num`; qualified, opened namespace and dot constructors | Name constructors and core quotation shorthands |
| Nat | numerals; `Nat.zero`, nested `Nat.succ`, including dot constructors | Nat literals/constructors and the fixed core OfNat instance |
| Int | numerals, unary minus; `Int.ofNat`, `Int.negSucc`; `OfNat.ofNat n`, `Neg.neg i` | Int constructors and the fixed core OfNat/Neg instances |
| Bool/String | true/false constructors and string literals | Bool constructors and string literals |
| Optional/array | `none`, `some literal`, `#[literal, …]` | Option constructors and core List.toArray/Array.mk constructor trees |
| Contract records | complete structure literals, anonymous constructors, fixed named constructors | exact schema constructors |
| Parentheses/ascriptions | parentheses on literal terms; `(literal : T)` for the exact literal or record type, with qualified or opened short spelling | the corresponding literal/constructor expression |

Array and Option type ascriptions, user aliases, references, updates and
computations are outside this grammar and receive
`contract.source_literal:nonliteral`. The expression decoder separately verifies
constructor arities and exact core numeric instances.

For metadata syntax, discovery reads macro and term elaborator registration keys
from the entry module’s compiler import DAG, plus source patterns for local
rules. A repository extension capable of processing a metadata node receives
`contract.source_literal:term_expander`; the audit never invokes it. Parser
choices are checked across alternatives. Unrelated mathematical notation and
mathematical payload expansion remain available. Core numeric instances are
verified separately by the expression decoder.

The existing arena structure decorators are admitted as direct delegates to the
core structure elaborators: their module owner, private-aware identity and
compiled direct delegation shape and marker body SHA-256 are checked. They annotate mathematical arena
expressions without changing contract fields. Other repository term elaborators
on metadata syntax fail closed.

The four `Contract` interface modules accept imports, namespace/section
scaffolding, `open`, `universe`, documentation comments, and bare
`structure`/`inductive` declarations. Declaration syntax has a finite node
table in `Contract.InterfaceGuard.typeSyntaxKinds`: identifiers, numeric
literals, application, arrows/Pi binders, Sort/Type/Prop, parentheses, type
ascription, explicit/implicit/strict implicit/instance binders, explicit universe
arguments, universe max/imax/addition/parentheses, and the listed declaration,
field, constructor and documentation containers. Unknown nodes, defaults,
attributes, deriving, tactics, do, quotations and every elaboration node
(including `Lean.byElab`) receive
`contract.interface:command_not_allowed`; unknown node kinds include the
`type_syntax_not_allowed` suffix.
The lexical gate precedes the compiled companion inventory; names cannot grant
permission to rejected source commands.

Reg commands also have a complete finite command-kind table in
`Contract.SourceAudit.ordinaryRegCommands`. Only listed ordinary mathematical
and legacy registration scaffolding, bare `set_option` and allowed attributes
pass. The ordinary parser kinds are `declaration`, `end`, `moduleDoc`,
`namespace`, `open`, `printAxioms`, `section`, `universe` and `variable` in
`Lean.Parser.Command`. The legacy kinds in `LeanInformationAudit` are
`command__`, `registerInformationFiniteSourceTheoremCmd`,
`registerInformationSourceTheoremCmd`,
`registerInformationTheoremOccurrenceReadoutCmd`,
`registerInformationTheoremReadoutCmd`, `sealInformationTheoryCmd` and
`«command__Constructors_[_,,]»`.
`in` and `mutual` recursively audit their inner commands. Unknown commands,
`run_meta`, `run_elab`, macros, syntax, elaborators, initialization and evaluation
commands receive `contract.reg:metaprogramming_not_allowed`.

The sole `run_cmd` exception is the 84 exact module/syntax fingerprints in
`Contract.RegPolicy.catalogCommands`: 65 direct catalog literals, 16 snapshot
do bindings, and 3 named contracts. The entire tree contributes identifiers,
atoms, node kinds and child order; source positions and whitespace do not.
The final expression must be a one-argument call, whose name resolves uniquely
to `LeanInformationAudit.RootCatalogs.declare`. The three pinned named forms
use the existing `RootCatalogs.declare` short spelling under `open
LeanInformationAudit`; their resolved target is fully qualified. References,
quoted Names, suffix matches, changed arguments and additional statements
have no entry. No audit executes a source command or macro.

Local notation has exactly three module/syntax bindings:

| Module | Exact notation |
| --- | --- |
| `Reg.D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau` | `local notation "F" => Nat.fib` |
| `Reg.D5.S1.Recurrence.Invariants.CloitreActualSpineCarry` | `local notation "F" => Nat.fib` |
| `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost` | `local notation "kact" => fun K X => PhyslibLeaf.MatrixMap.of_kraus K K X` |

Changing the token or right hand term loses permission; duplicate catalog or
notation commands are rejected. Standalone `attribute` and `@[…]` accept
only `instance` and `reducible`, with no priority or other attribute arguments.
Local/scoped markers do not expand the attribute-name table. Unlisted names
receive `contract.reg:metaprogramming_not_allowed:…:attribute`.

Source `set_option` accepts exactly `autoImplicit`, `relaxedAutoImplicit`,
`backward.isDefEq.respectTransparency`,
`backward.isDefEq.respectTransparency.types`, `maxHeartbeats`, `maxRecDepth`,
`trace.InformationRegistration.check`, and `maxSynthPendingDepth`. Values are
literals of the option type: Boolean for the implicit/transparency/trace options,
Nat for the resource bounds. Name prefixes grant no permission. Other names
receive `contract.reg:option_not_allowed`; mistyped literals receive
`contract.reg:option_literal_type`.

Every Reg declaration rejects `unsafe` and `partial` with
`contract.reg:declaration_modifier_not_allowed`; `noncomputable`, `private`, and
`protected` remain permitted. These checks traverse the complete source trees,
including `in`, `mutual`, and command/term/tactic `set_option`. Unrecognized command
wrappers fail by name. Authored elaboration reads deduplicated origin commands,
including their wrappers.

Every audited Reg constant outside a validated contract entry is forbidden to
directly reference any constant owned by an imported
`LeanInformationAuditInterface.Contract.*` module in its compiled type or body.
The check uses `ConstantInfo.getUsedConstantsAsSet`, including opaque bodies,
and reads the explicit structure names of primitive `Expr.proj` nodes that Lean
`foldConsts` omits. Constructors, projections, Ref, readout and option types all
participate. It emits
`contract.reg:contract_reference_outside_entry`. No dependency closure, reduction,
carrier projection table, result-type shape gate or type-alias tracker is used.
Ordinary mathematical definitions and theorems obey the same rule without shape
restrictions. Entry heads, closed terms, literal metadata, Reg command permissions,
interface command permissions and source/compiled inventory reconciliation remain
checked.

Contract entries have no declaration suffix: `where`, termination hints,
`decreasing_by` and `deriving` receive
`contract.entry:declaration_suffix_not_allowed`.

Only `eq_1` and `eq_def` have entry auxiliary permission. Both must be
same-module theorem constants at Lean v4.33.0 reserved equation identities, with
the simple reflexive equation shape with the validated entry body as its right
hand side. Source
where/let-rec declarations retain their own authored inventory. Authored term
elaboration in the entry command tree, including imported repository
term/tactic/command expanders, grants no equation permission. Enclosing wrappers
remain in that tree; sibling declarations in a mutual block do not. Unrelated
mathematical declarations retain their ordinary syntax permissions. The import syntax keys are checked against the complete
source command trees. All other compiled constants,
including named elaboration children, obey the ordinary direct-reference rule.
Private compiler identities and source user spellings remain distinct.

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
and contributor identities retain the existing snapshot checks. Files at other
leaves that still use legacy catalog commands have a pre-migration state: the
path rule imposes ordinary typed-entry obligations until their migration moves
them to a reserved leaf and rewrites their entries.

Typed expected occurrences come only from RootCatalog. `ExpectedDeclaration`
remains an interface type for negative compatibility probes, but an entry of that
type always receives `contract.root_structure:independent_expected_not_allowed`.
Its decoder and snapshot output are absent; there is no independent-expected
fallback. Removing this type in P3 affects only the retired negative fixtures and
the interface companion inventory; P0 has zero production declarations of it.

The production report consumes legacy inputs pending the typed migration.
Existing Reg modules pass the command/reference audit; typed discovery finds
zero production typed entries. P2b splits catalogs and seals from D5 mirrors
into `Reg/Catalogs/D5/<D5 relative module path>/RootCatalog.lean` or
`SealedCatalog.lean`. Mirrors retain their registrations at their original paths;
catalogs import those leaves, and leaves do not import catalogs. Catalog root IDs
use the catalog module; registrationModuleName retains the leaf owner. P3
installs typed discovery and removes the pinned legacy command permissions.
Catalogs and seals are optional analysis groups: registration assessment does
not require catalog membership. Missing seals remain visible as absent report
artifacts; migration correspondence is checked separately.

The compiled interface inventory admits only source types, kernel constructors,
recorded projections and the pinned compiler's explicitly listed recursor,
noConfusion, constructor and sizeOf companions. Unknown compiler products
receive `contract.interface:compiled_non_type`.

P2b rewrites all 544 legacy commands (426 registrations, 23 enrollments,
84 catalogs and 11 seals), the three local notations, and all attribute/reducible
uses to the fixed grammar. P3 removes all 84 catalog `run_cmd` permissions and
their table, all three notation permissions and their table, the temporary
instance/reducible attribute permissions, and legacy registration/enrollment/seal
command kinds. Attribute uses required by mathematical code must first be
expressed by the fixed grammar rather than retained as exceptions. P3 also deletes
the four legacy evalExpr paths; typed discovery has no evaluation fallback.

[CI](../../.github/workflows/ci-current.yml) 和本地数学门通过 `make lean-report`
调用同一个 `inspect.sh`。入口可独立构建 utility 输入工具,也可接收显式的
`STRATALINT_LEAN_PRODUCER_DLL`。生成的报告交给 check-current/check-delta;
这些检查器不生成报告。离线 truth/export 与 bundle 验证工具保留,不提供
自动选择 CI 来源或发布资格的链路。

输出采用 `stratalint-raw-lean-report-v2`，同一文件名后附
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
`report_cache_release_semantic_version` 决定还原后的报告复用；验证器只查结构与工件完整性。
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
报告是否可复用由 Lake trace 和 `report_cache_release_semantic_version` 决定。正常入口在 ensure 前不创建
默认输出或日志目录，以保留新工作树的 donor 播种条件。

程序编译义务由 `inspect.sh` 的默认目标选择；直接调用可用排序后的 JSON 列表通过
`STRATALINT_LEAN_BUILD_TARGETS` 覆盖。报告、materials 与这些构建产物随项目
`.lake/build` 缓存运输，不另建报告缓存。
正常入口校验可选 `.reuse.json`：报告语义版本号、登记的报告模块与配置输入及其 mode、显式工具/环境/平台与上轮成功调用
一致，并且报告五件套与收据逐字节相符、信封和输入坐标仍为当前时，复用报告数据。选中的程序目标仍须通过 Lake 增量编译；未选程序目标的命中不恢复 Lean 重缓存。
缺失、损坏或不匹配时，同一次 Lake 调用构建 `:report` 和选中的程序目标。生产程序（含 Lean Inspector/audit、C#、脚本、构建属性）的字节不进入该收据，其兼容性只由 `report_cache_release_semantic_version` 表达；实际构建或检查失败仍失败，缓存命中不能代替判词。未提供覆盖值的直接调用使用 Inspector 默认程序目标。
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
仅登记为 producer、未进入模块或 utility claim 依赖闭包的文件，不会因此使报告失效。

清单中的单一正整数 `report_cache_release_semantic_version` 是开发者维护的报告语义兼容版本，
其值以清单为准，与清单格式的 `schema_version` 分开。

兼容的生成器重构、性能优化保持 `report_cache_release_semantic_version` 不变：在报告输入、配置及
版本均未变时，仅 producer 源码或可执行文件字节变化不会强制重提取有效模块报告，
进入原生生产或选中 inspector 程序目标时，当前 inspector 仍须编译成功。改变报告含义或接受语义时必须增加此版本，例如改变
声明选择、statement identity 计算或 utility 证据含义；即使 JSON schema 完全相同
也须 bump。例如从 `3` 增加到 `4` 会使全部模块报告及汇总失效，即使最终 report 和
materials 的内容字节相同。版本是明确的兼容承诺，不是机器自动判定源码编辑是否兼容。

[原生依赖](lakefile.lean)按以下输入决定报告工作：
逐模块工件 trace 只取模块及 utility claim 的编译闭包与语义版本；固定 judge 驱动和 inspector 程序仅等待构建成功，不额外混入其 trace 或源码绑定。
enrollment plan 不保存源文件字节摘要；plan identity 与模板 assessment 消费编译信息，导入源码的纯注释编辑不改变它们。

| 输入变化 | 失效范围 |
| --- | --- |
| `report_cache_release_semantic_version` 增加 | 所有模块报告及汇总。 |
| 模块源文件、编译工件或传递 import 工件变化 | Lake 依赖 trace 对应的模块报告；模块自身源码逐字节追踪，导入模块只按编译工件追踪，注释不改变编译工件时复用导入者。 |
| 模块 utility 记录变化 | 对应模块报告；声明的 claim 源码、编译工件及其传递依赖同样参与，即使 claim 不在 result 的 import 闭包内。 |
| 登记的 `config_inputs` 文件字节变化 | 通过 Lake 影响实际编译依赖；整体配置身份只影响聚合。 |
| 登记的模块成员集合变化 | 汇总按当前集合重建，新成员执行所需报告工作，保留仍有效的模块工件。 |
| 固定 Registry 驱动及其传递编译工件变化，语义版本不变 | 仅自身或 utility claim 的编译闭包实际导入该模块的报告失效；其他报告复用，驱动仍须构建成功。 |

`information_templates` 分区携带 occurrence inventory 和 BindingRecord，
其 `compatibility_version` 等于 manifest 的缓存发布版本；复用验证检查结构，不重算当前源码摘要。
C# 消费者另行检查完整证据语义、sidecar 归属及 debt 约束。固定驱动属于 judge，
没有模板模块的隐式导入。独立编码测试使用显式 `--statements-only`，其结果不含
binding evidence，不能通过声明模板的严格消费者。
`InlineRealization.lean` 编译时要求实际导出的 inline provenance wire 等于它 import 的 `InlineProvenanceWire.canonical`，C# 测试读取同一字面量验证消费契约；该字面量是 Lean 源，由 Lake 的 import 追踪；bump `report_cache_release_semantic_version` 时同步更新其中的 `compatibility_version`。

Lake 的 `transImports` 为模块及其 utility claim 选择传递源码依赖；编译工件 trace
包含 inspector 私有导入所需的传递依赖。捕获结果写入模块输入旁的 `.sources.json`，
由 [native producer](native.py) 检查本地路径均在上述登记范围内。
报告行只保留自身的 `source_path`/`source_sha256`；
导出证据和来源 sidecar 不重复存储导入源码的原始摘要。
外部包依赖由登记的 Lake manifest pin 约束。

兼容身份与实际产地分别记录。[provenance-v2](publication.py) 的
`producer_sha256`、`repository_inspector_sha256` 承载语义兼容标识；实际生成来源的摘要记在
`module_origins` 各模块的 `producer_sources_sha256` 和
`inspector_executable_sha256`，并绑定该模块报告哈希。复用保持原始来源，增量汇总可含
多个真实来源；`mode=cached` 或 `produced` 描述本次发布工作，不把旧报告改称当前
可执行文件新生成。

导出的 bundle 以 `module_origins.report_sha256` 检查来源记录与报告行的完整性。
发布和导出报告的 [输入验证](../scripts/report/lean-report-input.sh) 核对来源记录、模块成员与登记路径，
不重算当前源码、claim 源码或捕获依赖的文件摘要来决定复用。
inspector 不兼容改动手动 bump `report_cache_release_semantic_version`。
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
| 工件缺失且无法由 Lake 恢复，或输入/语义版本/编译产物变化需要重建 | 非零退出，报告目标需要重建。 |

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
