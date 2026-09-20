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

[CI](../../.github/workflows/ci-push.yml) 与本地 `make current` 共用入口，
经 `make lean-report` 调用同一个 `inspect.sh`。工程阶段已验证的候选 Lean DLL
通过 `STRATALINT_LEAN_PRODUCER_DLL` 传入，独立调用才构建 utility 输入工具。
[Release](../../.github/workflows/truth-release-publish.yml) 选择指定 dev 源码的成功
push engineering/current 及其报告工件，经共同交接入口校验候选、轮次和完整材料后使用。
缺少该源码的合格报告工件时不能发布，不在消费者中重产报告。

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
入口完成当前默认目标、原生报告及完整校验，再打包根 buildDir；不另跑一轮 `lake build`。
输入、编译或报告校验失败即发布失败，即使本轮发布地址已存在也不能绕过。
归档携带原生 Inspector 可执行文件、模块与汇总工件，以及规范报告、materials、origin 和
attestation。发布继续使用 mathlib 分区内的 run/attempt 快照及 draft 上传协议；draft
不能作为可用种子。传输失败不改变已经完成的构建与报告结论。
旧两段或三段哈希的 `lean-cache-v1` 归档都只作为同 mathlib/平台的增量种子，消费时核对
manifest 与 tag 的声明地址；不恢复 config/exact/same-toolchain 选择。原生 trace 与完整
当前输入和 materials 校验决定还原后的报告复用。
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
报告是否可复用仍由 Lake trace 和 inspector 校验决定。正常入口在 ensure 前不创建
默认输出或日志目录，以保留新工作树的 donor 播种条件。

每次 `make lean-report` 都要求当前项目默认目标和 inspector 编译的有效成功证据。
正常入口先校验可选 `.reuse.json`：报告语义版本号、登记的 Lean 源与配置输入及其 mode、显式工具/环境/平台与上轮成功调用
一致，并且报告五件套通过完整私有校验时，复用该调用而无需下载 Lean 重缓存。缺失、损坏
或不匹配时进入原生 Lake 增量；生产程序（C#、脚本、构建属性）的字节不进入该收据，其兼容性只由 `report_cache_release_semantic_version` 表达；实际构建或检查失败仍失败，缓存命中不能代替判词。[当前默认目标](../../lakefile.toml)为 `Trureturing` 和
`LeanInformationAudit`。默认目标及 audit 的构建义务独立于模块报告失效；只影响这些
构建义务、未改变报告依赖的编辑，不会因此重提取无关模块报告。实际缺失或失效的模块
提取会合批以共享加载工作，失效选择仍由 Lake 决定。输出
`LEAN_INSPECTOR_WORK extracted_modules=… aggregates=…` 分别表示本次实际提取模块数
与汇总次数。输入未变且原生工件有效时，两者均为零；完整调用复用时仍校验构建成功证据
与报告材料，current/delta 检查继续执行。
这两个计数不表示 Lean 重编数量；进程 RSS 观测也不表示最低 RAM 要求。

[lean-report-inputs.json](../../lean-report-inputs.json) 是 FILEMAP 登记的唯一输入
清单，声明 `report_modules`、`inspector_sources`、`config_inputs`、
`producer_scopes`，并可声明 `dependency_sources` 和完整调用的 `report_execution` 环境。
只有成功完成默认目标、report 和发布的入口才封存 `.reuse.json`；该证据随 current
种子传输，不改变报告 schema、模块来源或远端 mathlib 分区。
[读取器](../scripts/report/lean-report-selection.py) 只展开显式登记的路径集合；路径为
大小写敏感的仓库相对 POSIX 路径，按 `include`（`pattern`、`optional`）及 `exclude`
选择，报告模块必须能在 Lake workspace 中解析。`dependency_sources` 与 `report_modules`
共同给出允许捕获的本地 Lean 源码范围；它是登记清单，不是另一套失效规划器。
仅登记为 producer、未进入模块或 utility claim 依赖闭包的文件，不会因此使报告失效。

清单中的单一正整数 `report_cache_release_semantic_version` 是开发者维护的报告语义兼容版本，
其值以清单为准，与清单格式的 `schema_version` 分开。

兼容的生成器重构、性能优化保持 `report_cache_release_semantic_version` 不变：在报告输入、配置及
版本均未变时，仅 producer 源码或可执行文件字节变化不会强制重提取有效模块报告，
但当前 inspector 仍须编译成功。改变报告含义或接受语义时必须增加此版本，例如改变
声明选择、statement identity 计算或 utility 证据含义；即使 JSON schema 完全相同
也须 bump。例如从 `3` 增加到 `4` 会使全部模块报告及汇总失效，即使最终 report 和
materials 的内容字节相同。版本是明确的兼容承诺，不是机器自动判定源码编辑是否兼容。

[原生依赖](lakefile.lean)按以下输入决定报告工作：
逐模块工件 trace 只取模块及 utility claim 的编译闭包与语义版本；固定 judge 驱动和 inspector 程序仅等待构建成功，不额外混入其 trace 或源码绑定。

| 输入变化 | 失效范围 |
| --- | --- |
| `report_cache_release_semantic_version` 增加 | 所有模块报告及汇总。 |
| 模块源文件、编译工件或传递 import 工件变化 | Lake 依赖 trace 对应的模块报告；源码哈希也独立参与，包含只改注释的编辑。 |
| 模块 utility 记录变化 | 对应模块报告；声明的 claim 源码、编译工件及其传递依赖同样参与，即使 claim 不在 result 的 import 闭包内。 |
| 登记的 `config_inputs` 文件字节变化 | 各模块报告的共同依赖，包括 toolchain、依赖 pin 和 Lake 配置。 |
| 登记的模块成员集合变化 | 汇总按当前集合重建，新成员执行所需报告工作，保留仍有效的模块工件。 |
| 固定 Registry 驱动及其传递编译工件变化，语义版本不变 | 仅自身或 utility claim 的编译闭包实际导入该模块的报告失效；其他报告复用，驱动仍须构建成功。 |

版本 4 的 `information_templates` 分区携带 occurrence inventory、BindingRecord 和
当前源码输入。原生复用和发布检查这些输入的字节绑定；陈旧或缺失输入使工件失效。
C# 消费者另行检查完整证据语义、sidecar 归属及 debt 约束。固定驱动属于 judge，
没有模板模块的隐式导入。独立编码测试使用显式 `--statements-only`，其结果不含
binding evidence，不能通过声明模板的严格消费者。

Lake 的 `transImports` 为模块及其 utility claim 选择传递源码依赖；编译工件 trace
包含 inspector 私有导入所需的传递依赖。捕获结果写入模块输入旁的 `.sources.json`，
由 [native producer](native.py) 检查本地路径均在上述登记范围内，再记录路径到
SHA-256 的 `input_sources`。每行记录自身源码和未单独出现在报告中的本地依赖；
其他报告模块的源码由完整报告的成员与源码绑定覆盖，避免逐行重复整份闭包。
外部包依赖由登记的 Lake manifest pin 约束。

兼容身份与实际产地分别记录。[provenance-v2](publication.py) 的
`producer_sha256`、`repository_inspector_sha256` 承载语义兼容标识；实际生成来源的摘要记在
`module_origins` 各模块的 `producer_sources_sha256` 和
`inspector_executable_sha256`，并绑定该模块报告哈希。复用保持原始来源，增量汇总可含
多个真实来源；`mode=cached` 或 `produced` 描述本次发布工作，不把旧报告改称当前
可执行文件新生成。

导出的 bundle 保留 `module_origins.input_sources`。原生模块接受时核对本次 Lake
捕获的依赖集合及当前哈希；发布和导出报告的
[当前输入验证](../scripts/report/lean-report-input.sh) 核对来源记录、模块成员、
源码、claim 源码和捕获依赖的当前文件字节，拒绝未登记或陈旧的绑定。
兼容 producer 改动不要求旧行的生成指纹等于当前 producer；重新生成的行才记录新指纹。
仓库输入地址与 provenance 的 `input_address` 由同一输入工具按各自编码计算，
不能互换，commit ID 与工作树名称不参与这些地址。

缺失的可选原生工件由 Lake 恢复或补建。存在但损坏或不兼容的工件先被拒绝，再在私有构建树
重建一次，该次恢复禁用缓存读取；重建仍无效则失败。默认输出或任一相邻 sidecar
丢失、损坏时重新运行 `make lean-report`，它从已验证的 inspector 工件重新发布，
必要时先补建。接受前仍检查规范 JSON、materials 身份、provenance、当前源码、utility
绑定及输入坐标，不能把缓存命中当成检查通过。

原生 Lake `--no-build` 保留上述接受条件：

| 工件状态 | `--no-build` 结果 |
| --- | --- |
| 所需构建目标已就绪，报告工件有效且输入未变 | 校验后复用，零提取、零汇总。 |
| 工件缺失且无法由 Lake 恢复，或输入/语义版本变化需要重建 | 非零退出，报告目标需要重建。 |
| 模块或汇总工件存在但损坏、缺失来源绑定或不兼容 | 非零退出；在修复提取或汇总之前拒绝，不删除或改写被拒工件。 |

已用 `make lean-report` 准备好工具和私有 `.lake` 后，可以检查原生报告目标：

```sh
tools/scripts/worktree/lean-cache-run.sh lake --no-build build :report
```

该命令经同一 writer 入口运行，只检查原生目标，不发布到 `LEAN_REPORT`。
`--no-build` 限制 Lake 的重建，输入准备、校验及可用原生工件的恢复仍会执行，
不是整个入口的只读模式。需要修复时重新运行 `make lean-report`。

[完整校验](publication.py) 保留每条声明的 `statement_id`、`type_sha256` 和规范
material 校验，`include_in_statement=false` 的声明也须有对应材料。共享校验可在
单次调用内复用已计算的声明身份，但仍读取、CRC 检查并哈希实际材料字节。
当前输入验证不替代完整 materials 校验；报告发布前两者均须通过。

必需输入错误直接失败：清单缺失或损坏、版本缺失或非正整数、必需登记无匹配文件、
不安全或穿越 symlink 的路径、模块冲突或无法解析、无效的 utility/claim 输入均不
通过；不会猜测输入或把错误降为缓存未命中。只声明为 `optional` 的缺项可被接受。
Lean、audit、工具构建和发布失败也返回非零。阶段失败输出会指出
`LEAN_INSPECTOR_FAILED phase=… exit=…` 并打印诊断；ensure 成功后，各阶段诊断保存在
所选输出文件名后附的 `.logs/` 目录中。修正具名输入或构建错误后，仍使用同一
`make lean-report` 入口重试。
