# trureturing 工程优化方案 v1.0

**定位：保持数学与准入语义的规模化工程设计。**  
**文档状态：** 工程规则与数学优化边界。生产实现以当前契约类型、编译产物读取路径与严格报告格式为准；数学优化不得改变准入条件。

## 0. 核心决策

保留一个逻辑与治理根，先在现有仓库内完成模块化，不先引入多仓库、微服务或新的构建系统。Lean 继续负责数学对象与证明，Lake 负责构建依赖，StrataLint 保留现有治理职责，Scribe 保留叙述产物职责。外部缓存、索引和调度均不取得数学裁判权。

数学真值由 Lean 内核检查的声明与证明承载；准入按现行契约与判官规则执行。
判官自身测试和对当前编译输入的完整报告评定验证实现，不以旧判官的判词、
报告或 seal 导出包逐条一致作为验收。文件、缓存与流程检查不冒充形式证明。

### 0.1 数学义务与报告评定

SealCatalog 的逐成员结论允许 positive 或 zero；zero 携带平凡性与剩余目录的闭包归属证明。
目录结论允许 redundant 或 irredundant。报告核对编译字段与完整目录，
不重新计算增益，也不把冗余目录作为一律拒绝的输入。

### 0.2 一次编译的准确合同

冷工作树仍从现有 `make lean` / cache-writer 入口进入，不能先裸跑 Lake 破坏 donor 初始化条件。一个顶层构建调用中，Lake 可以按 DAG 编译多个文件、复用已有产物，Reg 的 `Contract.Seal` 在编译期检查同一目录上非退化性、bundle 非空、逐成员降低逃逸或平凡性及闭包归属、kernel 碰撞与目录结论的数学义务，报告仅消费编译字段。禁止“先外部生成证明源码，再启动第二轮编译完成证明”的新链条。

缓存依赖过往计算，不等于把历史版本引入信息增益的数学定义。性能对照版本与 Git 治理 protected-base 也不等于数学 baseline，三者必须分别命名。

---

## 1. 当前源码事实与优化落点

| 已核对路径 | 当前行为 | 结论 |
|---|---|---|
| `lakefile.toml` | 根包管理数学内容；Interface、Impl、Reg 与测试宿主独立分包 | 优化不能简单删默认覆盖；先保持全覆盖、做增量复用 |
| `Makefile` | 已有 `make lean`、`lean-report`、`gate`、发布与取回缓存入口 | 扩展现有入口，不叠加第二套命令体系 |
| `tools/lean-inspector/Inspector.lean` | 用 `RawArtifacts.Store` 读取编译部件，按模块流式输出报告 | 按实际输入闭包和批次边界测量读取成本 |
| 同上 | 公理闭包已有 Tarjan SCC 与运行级共享缓存 | 保留；不能将“新增 memoization”当作本轮主要收益 |
| `lakefile.lean` / `native.py` | Lake trace 决定编译产物和整份报告复用 | 实现字节不进入报告复用条件 |
| `materials.py` / `publication.py` | 校验并发布 canonical 报告与材料 | 按实际分配量测量内存 |
| `CompiledSeal.lean` | 按 `arenaName` 分组、确定顺序、构造当前目录 | arena 是语义边界，不是可以任意改的小批次 |
| `Contract/Catalog.lean` | SealRow 承载逐成员结论；SealCatalog 将数学证据绑定同一单位向量目录 | 数学证据在 Reg 编译期检查 |
| `ExactRate.lean` | 已证明 `escapeNumerator_without_eq` 等式及正增益刻画 | 可直接复用，避免重新枚举每个留一族 |
| `CompiledSeal.lean` | 消费编译期已检查的 Seal；报告期核对目录身份、arena、成员顺序与完整单位向量 | 保留原子性，增强文件发布与编译产物绑定 |
| `README.md`、缓存归属文档 | 私有工作树、禁止 symlink 共享 `.lake`、已有 clonefile/donor | 不以移除互斥锁或共享可写目录换性能 |
| `.github/workflows/ci-current.yml` 与 `ci-unit.yml` | `detect` 作业按 workflow 内的单元白名单决定各单元作业是否命中；current 构建一次报告并随项目 buildDir 缓存运输 | 单独处理可选缓存传输失败；真正检查失败仍阻断 |

上述为源码审查，不是耗时排行。必须先测量各阶段 wall time、CPU、RSS、读写与锁等待，再决定并行度和批量大小。源码显示重复工作，不自动证明它是部署环境的最大耗时。

---

## 2. 包架构与职责

Interface 定义依赖数学类型的契约。Reg 依赖根数学包与 Interface，
声明契约类型的数据与证明字段，不依赖 Impl。Impl 读取编译部件并评定登记；
`tools/lean-inspector-reg` 是依赖 Reg 与 Impl 的测试和分析宿主。

生产报告入口构建登记的程序目标与报告 facets，输出当前格式的报告和材料。
StrataLint 消费显式报告执行准入，Scribe 生成叙述投影。
报告、缓存及来源摘要均不替代 Lean 证明项。

---

## 3. 四种依赖图必须分开

### 3.1 构建图 G_build

节点为模块与 Lake facet；边来自 Lean imports、插件、代码生成和显式构建依赖。谁需要重编译，由 Lake 与真实输入决定。不能仅凭“定理陈述没变”复用本该失效的环境。

### 3.2 证明审计图 G_proof

包括声明的类型、证明体、定义体、构造器、归纳类型及公理闭包依赖。允许声明级相互递归，因此 SCC 处理不可删。不能用只扫描定理正文中的显式名字替代完整依赖收集。

### 3.3 信息目录图 G_information

节点包括登记、theorem unit、arena、primitive bundle 与完整有序目录。编译输入的变化由 Lake 依赖 trace 传播；报告消费当前 import 闭包中的目录与快照，不维护独立的目录证书缓存。

### 3.4 叙述与发布图 G_document

节点包括 GID、Scribe AST、声明投影、覆盖边、页面与目录。Lean 陈述未变、只改叙述时，不必重复检查数学；但必须重新生成受影响叙述与覆盖产物。

统一目录提供关联，不把这四张图强行当成同一张失效图。各图的删除、重命名、依赖增加都纳入回归测试。

---

## 4. 报告工作观测

`LEAN_INSPECTOR_EXTRACT`、`LEAN_INSPECTOR_ASSESS` 与 `LEAN_INSPECTOR_WORK` 描述本次模块工作。
`STRATALINT_INSPECTOR_MODULE_WORK` 可指定模块工作 JSONL；这些观测不参与 trace 或准入。
`LEAN_REPORT_CACHE_MISMATCH` 给出新增、删除、改变的输入数及执行环境是否改变。
编译与报告提取分别复用，seed 被拒绝本身不证明全库重编。

---

## 5. Inspector 输入、分批与输出

### 5.1 请求与模块覆盖

`native.py` 从当前选择器取得模块与 utility 输入。批次请求写入 JSON 文件，
以 `--request-file` 交给 Inspector；模块输入为 module、source path、source hash 三元组。
批处理按模块名排序，拒绝重复模块与不同 root／executable 的混合请求；
每个固定大小的 chunk 再分为普通提取与有登记输入的评定组。
输出模块数组必须与该组的预期模块集合完全一致。

### 5.2 编译部件与流式陈述

Inspector 使用 `RawArtifacts.Store` 读取编译部件，对目标模块执行提取与登记评定。
statement-v1 编码通过有界字节缓冲写入 spool；名称、universe、表达式与
定义体沿原规范编码，metadata 保留编码标记。公理闭包使用 SCC 与运行内 memo。
这条读取路径不加载 Lean Environment 或执行证明项。

### 5.3 当前报告与复用

公开报告格式为 `stratalint-raw-lean-report-v3`，严格读取器只接受该格式。
提取语义或公开格式改变须更新格式标识并全部重提取。
模块 facet 以编译器产物闭包、utility 输入及格式标识决定 ZIP 复用；
判官程序必须构建成功，其字节不进入报告 trace。
聚合 facet 核对完整模块成员并合并材料，完整调用收据校验报告五件套。

---

## 6. Lean 数学计算优化：先融合扫描，再做分区索引

令同一 arena 的状态数为 N，定理数为 m。所有公式均针对现有有限非退化 arena，不改变状态权重与目录。

### 6.1 P1：对每个状态对只扫描一次定理族

对有序非对角对 p=(x,y)，定义：

\[
D(p)=\{i:\neg\operatorname{agrees}_i(x,y)\}.
\]

分类只有三种：

- D 为空：计入全量逃逸 C。
- D 恰为 {i}：计入该 i 的独有捕获 U_i，并计入该对的四角色 signature bin。
- |D|≥2：不计入 C 或任何 U_i，可以在第二个不一致时结束本对扫描。

由定义得到：

\[
C=\#\{p:D(p)=\varnothing\},\qquad
U_i=\#\{p:D(p)=\{i\}\}.
\]

随后直接用现有 `Catalog.escapeNumerator_without_eq`：

\[
C_{-i}=C+U_i.
\]

这一步不需要减法，也不需要重新枚举 leave-one-out 集合。

计算为逐对 streaming fold，不先构造 `X × X` 的完整 materialized array。先保持有序对；若以后只扫描无序对、贡献乘 2，必须先证明所有相关同意关系、角色 signature 对调对称。

若一次 primitive agreement 视为单位成本，融合方案最坏扫描量为 O(N²m)，计数器为 O(m) 加固定 15m 个 histogram bin。它减少逐定理重复扫描其他定理导致的重复因子；真实收益还包含 primitive 的成本和 kernel 检查成本，不能仅凭 Big-O 声称整库加速比例。

### 6.2 P2：有精确可计算类标签时，用分区计数

如果联合读出把 X 分成大小为 n_1,...,n_r 的纤维，则：

\[
C=\sum_{j=1}^{r}n_j(n_j-1).
\]

构造精确 prefix/suffix 类编号：

\[
P_i(x)=[(c_0(x),...,c_{i-1}(x))],
\quad
S_i(x)=[(c_i(x),...,c_{m-1}(x))].
\]

删除 i 后，用 `(P_i(x),S_{i+1}(x))` 分类。其直方图给出 C_{-i}，再由已证明的加法关系恢复 U_i。以自然数相减实现时必须携带 C≤C_{-i} 的证明，不能用截断掩盖错误。

**复杂度边界：** 若已拥有精确的有限类标签，prefix/suffix 可避免复制长度 m 的留一向量；排序实现通常约 O(mN log N)，哈希索引为有条件的期望复杂度。只给 `DecidableEq` 或任意 kernel predicate 时，生成标签自身最坏可需要二次比较。必须把这一步和其证明成本计入，禁止宣传普遍线性时间。

哈希只定位桶，碰撞后必须比较精确键。哈希相同不构成 Lean 相等证明。

### 6.3 15 类角色直方图不能被优化“丢掉”

融合扫描天然可产出所有 bin。分区路径使用固定四角色上的精确包含—排除。

令 R={CUT,FLOW,ADMIT,ANCHOR}。对 T⊆R，M_i(T) 是“所有其他定理都同意，且 i 的 T 中各角色都同意”的有序非对角对数。通过附加这些角色类标签的直方图计算。

若某状态对恰在角色集合 B≠∅ 上分离，则其计数为：

\[
H_i(B)=\sum_{U\subseteq B}(-1)^{|U|}
 M_i((R\setminus B)\cup U).
\]

并需证明：

\[
H_i(B)\ge0,\quad
\sum_{B\ne\varnothing}H_i(B)=U_i,\quad
M_i(R)=C.
\]

只有在四角色 kernel 与当前 `roleSignature` 语义的对应已被证明后，才能接入该路径。否则继续使用融合扫描，不能为了速度少输出角色信息。

### 6.4 库内融合计数

`D5/S3/ConceptDynamics/InformationEscapeCounting/Fused.lean` 定义融合扫描、
full／unique／without 与 15 类角色计数；`FusedCorrectness.lean` 给出与原计数定义的对应。
`Enumerations.lean` 提供具体 arena 的有限枚举。
这些数学计算用于构造编译期证据，生产报告不输出这些计数或角色桶。

---

## 7. 分块计算不等于缩小比较范围

同一 arena 可以按状态对域分块：例如第 k 块负责一段左状态序号及全部右状态。每块必须比较**完整 m 条定理**。

块输出：

\[
(C^{(k)},U^{(k)}_0,...,U^{(k)}_{m-1},H^{(k)}).
\]

在块互不重叠、并集精确等于非对角对域的前提下，合计得到全量向量。

不能分成“模块 A 里的定理互相比一次，模块 B 里的定理互相比一次”再各自声称正增益。两个完全重复的读出在完整目录中具有 U=0；目录可用 zero rows 与 redundant 结论承载该结果。

每个块的正确性证明绑定完整目录对象和 arena，不只绑定一个脱离语义的 JSON 哈希。跨进程调度传递对象地址，但最终 Lean 证明必须通过实际类型、目录及覆盖定理组合。

---

## 8. 契约证据：共享已检查结果，不重复展开同一大计算

`Contract.SealCatalog` 把 arena、size 与 units 绑定为同一 `Catalog.ofVector`。
nondegenerate、bundleNonempty、rows、collisions 与 conclusion 承载类型化证据，
enumeration 指定有限状态枚举。`SealRow` 只含 positive 或 zero 结论；zero 同时
携带平凡性和剩余目录的语义闭包归属证明。目录结论为 redundant 或 irredundant。
这些义务由 Reg 编译期内核检查；判官不生成计数证书或统计投影。

库内数学计算可复用已证明的融合计数或分区公式，用于构造上述数学证据。
辅助计算不自动成为新的 theorem unit，数值与原定义的关系仍须由 Lean 证明。
不得用 kernel 不检查的 native 结果替换证明。分别测量计算、证明构造、
内核检查和证明体大小，不把计算快等同于证明检查快。

`CompiledExpressions.sameShape` 对编译器已检查项作有界语义比较，不承诺定义相等。
其 `Decidable.decide` 分支只比较命题：同一命题的任意判定实例产生命题相等的
布尔值（Lean 的 `decide_eq_decide`），因此只略过该函数的判定实例参数。
其它实例或字典不受这条规则影响；不支持的形式保留具名失败。

---

## 9. 封印、快照覆盖与发布原子性

`Contract.Seal` 在 Reg 编译期承载完整目录的类型化数学证据；`CompiledSeal.lean` 在报告期核对编译字段，不安装声明或构建环境。报告通过现有 producer 的原子发布边界输出。

当前目录核对包括独立快照的成员与身份、source 唯一性、qualified-name 碰撞、
当前 arena、目录大小与标识，以及单位向量的每一项。目录数据与数学证明字段
由同一编译契约绑定；报告不生成目录证明。

编译部件只覆盖自身 import 闭包，不能仅凭局部闭包就声称“已经看见仓库全部注册项”。项目级覆盖清单必须来自确定的源快照与已有枚举器，并验证完整集合。该清单证明工程覆盖，不冒充“枚举了数学世界所有定理”。

Reg 契约先通过 Lean 编译，文件发行再验证 `.olean` 等构建产物、JSON/材料及 checksum。最终发布服从现有 producer 的原子文件边界；报告期不操作 Lean 环境。

模块 ZIP 与聚合 ZIP 在临时目录中构造后用 `os.replace` 发布；批次 pending 文件由 Lake 在成功后 rename，并在 finally 中清理。JSON 输出本身不证明 Lean 编译成功。

---

## 10. 契约接口与判官实现

Reg 只依赖根数学包与 Interface。判官实现变化不重编 Reg，整份有效报告复用；
编译输入闭包变化的登记由当前判官评定。
契约接口升级须在同一次交付迁移全部用法，删除旧表示；
编译依赖传播重编与重评。提取语义或报告格式变化更新报告格式标识，
严格读取器拒绝其它格式，不设置历史兼容读取路径。

---

## 11. 重型外部库适配

为 FLT 等设置独立的锁定构建单元。记录源 commit、Lean/Mathlib exact pin、补丁、许可证、公开定理陈述、定义对应、完整公理闭包、构建与重放收据。

先有契约明确的适配器，再引入真实证明。轻核心可以证明 `FLT -> Q`；只有同一兼容 Lean 环境中接入实际 `p : FLT`，才能交付无条件 Q。跨不兼容 toolchain 的 JSON 证书不能直接当成 Lean 证明。

工具链不一致时，选择协调到经过验证的共同版本，或暂时保留隔离结果而不冒充已链接。不要让依赖解析器悄悄用上游库自己的 Mathlib 替换主库定义。

测三条路径：从源码构建、只导入并使用一次、完整独立重放。三者资源数据不能互相替代。未测量前，不承诺任何轻接口的 MB 数值。

---

## 12. 报告工件与缓存边界

### 12.1 原生报告工件

`.lake/build/lean-inspector/modules/<module>.zip` 保存模块报告与材料；
`report.zip` 聚合完整模块集合。Lake trace 决定模块工件复用。
完整调用的 `.reuse.json` 绑定 report_modules、config_inputs、报告格式、
显式执行环境及报告五件套，并要求 defaults、report、publication 三阶段完成。
判官实现字节不进入复用条件。

### 12.2 来源与验证

模块 provenance 保存实际生成者与输入投影；实现变化不回写原生成者。
新生成模块在生产时验证报告、材料与 utility 绑定；聚合读取已生成的模块工件，
核对成员与来源结构。发布程序验证完整 bundle。
摘要与 provenance 是工程证据，不是数学证明。

### 12.3 失败处理

复用收据缺失、损坏或输入不符时，回到通常 Lake 路径。
作者输入登记错误仍是错误。编译、输入绑定或发布校验失败不发布成功结果。

---

## 13. 工作树、磁盘与生命周期

保持每棵工作树私有可写 `.lake`。已有 APFS clonefile 优先路径继续使用；其它文件系统的 copy-on-write/reflink 只能作为经过隔离验证的优化。禁止 symlink 共享可写缓存，禁止给可写构建文件建跨工作树 hardlink。

同一工具链下去重不消除多平台、多版本的真实成本。物理空间按平台/版本与保留策略核算，不使用文件表观大小冒充 APFS 物理占用。

---

## 15. CI 与单次构建整合

保留现有 required check 名称、merge-result 输入和 protected-base 治理逻辑。数学 no-baseline 不要求删除 Git 治理基线。

CI 的种子恢复步骤调用 `lean_actions.py restore`，从 Actions 缓存材料恢复依赖与项目种子并验证恢复目录；
不可用或无效种子不取得成功检查的资格。构建与准入检查保留各自失败退出。

`make lean-report` 通过缓存守门入口调用 Lake 的报告 facets。Reg 编译期检查契约数学义务，生产报告读取编译部件并评定结构，发布程序验证报告与材料。编译依赖 trace、utility 输入与报告格式标识决定增量复用；判官实现或规则改动不使报告失效，实现程序字节不进入复用条件。

接口升级须同一交付迁移全部用法、删除旧路径，经编译依赖自动重编并重评受影响的 Reg。实现改动不重编 Reg，整份有效报告复用，输入闭包变化的目标使用当前实现。提取语义或报告格式改变须更新报告格式标识，严格拒读旧格式并全部重提取。不得生成第二份证明源码、在报告期创建声明或保留旧路径回退。

---

## 16. 身份、模型和全局注册风险

三个不同的 ID 不能合并：

- 稳定逻辑地址：现有 GID、声明名称等，承载用户引用。
- 陈述/定义身份：现有 canonical 编码与依赖语义。
- 构建产物身份：工具链、选项、平台、源码与依赖产物共同确定。

同名不保证同义；定理类型摘要相同但所引用定义变了，也不能复用旧语义审计。发布清单必须能追踪定义环境。

增量扫描必须包括删除与重命名：旧图定位反向依赖，新源码提取新边。删除的模块不再是检查输入，但仍导入它的存活模块必须失败或修复。

类型化输入发现与公开/私有编译部件读取也要测试。编译 import 闭包中的登记必须完整发现，不能遗漏 peers 而使原本失败的目录通过。

---

## 19. 容量边界：优化不改变数学上限

对一个固定 N 状态的有限 arena，如果 m 条读出都拥有独有捕获见证，则 m≤N−1。因为无论以何顺序加入，每条都必须严格细分先前分区，而分区从一类最多增加到 N 类。

这是不可约读出族的限制，不是数学证明总数的限制。在“不改准入规则”约束下，工程不能让同一固定 arena 中任意多的读出全部正增益。重复或被替代的读出没有严格正增益，Seal 可用 zero row 与 redundant 结论表达。不得通过追加无语义标签、任选更大状态域或任意切分 arena 规避。

全库可以有多个已有、语义明确的 arena；优化复用各自结果，不强制把所有领域投进一个笛卡尔积，也不自动为提分而创建新 arena。新模型属于数学建模工作，应走原准入流程。

---

## 22. 回滚与验收

### 数学放行

完整目录的数学义务由 Lean 内核检查，报告核对当前登记、arena、成员顺序与单位向量。不以旧判官判词一致作为验收，不增加不允许的公理或隐藏前提。

### 工程放行

所有 expected module 均有且仅有一份当前格式结果；缓存丢失仍存在可信构建路径；坏缓存不能通过；工作树无互写；发布没有半成品；源码和正式收据历史保持。

### 失败边界

模块覆盖、登记绑定、契约解码或编译产物身份核对失败时具名终止，不发布成功报告。数学证明未通过内核检查时不能交付其结论。缓存缺失由现行 cache-writer 从当前源码重建；不回退旧判官、不双读旧格式、不改变快照换取通过。

---

## 23. 审查来源

下列仓库路径给出现行实现与数学定义。网络说明使用官方文档，具体特性以项目 pin 的真实编译结果为准。

[S1] `README.md`、`Makefile`、`lakefile.toml`。
[S2] `tools/lean-inspector/Inspector.lean`。
[S3] `tools/lean-inspector/inspect.sh`、`lakefile.lean`、`reuse.py`、`publication.py`。
[S4] `tools/lean-inspector/LeanInformationAudit/CompiledSeal.lean`。
[S5] `tools/lean-inspector-interface/LeanInformationAuditInterface/Contract/Catalog.lean`。
[S6] `tools/lean-inspector/LeanInformationAudit/CompiledSeal.lean`。
[S7] `D5/S3/ConceptDynamics/InformationEscape/ExactRate.lean`。
[S8] `docs/develop/spec/lean_single_compile_intrinsic_information_escape_theory_and_spec.md`。
[S10] `.github/workflows/ci-current.yml`、`tools/scripts/worktree/lean_actions.py`。
[S11] Lean 官方《Source Files and Modules》：`https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/`。
[S12] Lean 官方《Lake》：`https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/`。
[S13] Lean 官方《Validating a Lean Proof》：`https://lean-lang.org/doc/reference/latest/ValidatingProofs/`。
