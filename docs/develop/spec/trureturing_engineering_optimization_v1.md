# trureturing 工程优化方案 v1.0

**定位：保持数学与准入语义的规模化工程设计。**  
**审查快照：** `d0e63dda80290fc39bfc46fe8310b4b47a661e28`，`dev`，2026-09-05。  
**文档状态：** 规范性草案（Normative Draft）。本 PR 仅新增工程 SPEC，不实施代码改造，不改变数学与准入规则；未运行该仓库全量 Lean 构建。文中新增路径、数据结构和接口均为拟议项，不代表已实现。

## 0. 核心决策

保留一个逻辑与治理根，先在现有仓库内完成模块化，不先引入多仓库、微服务或新的构建系统。Lean 继续负责数学对象与证明，Lake 负责构建依赖，StrataLint 保留现有治理职责，Scribe 保留叙述产物职责。外部缓存、索引和调度均不取得数学裁判权。

优化分三条主线：

1. **少加载：** 按闭包成本分批检查、逐步迁移公开/私有模块、将巨型证明隔离到明确的集成目标。
2. **少重复：** 复用已证明的留一计数恒等式，一次统计所有定理的独有捕获；复用经检查的计数证明，避免再次 `decide` 同一全量命题。
3. **少复制：** 报告流式处理、内容寻址保存、保持工作树私有写入边界、显式管理缓存与档案生命周期。

首要不变量是：

\[
\operatorname{Admit}_{\mathrm{optimized}}(S)
\iff
\operatorname{Admit}_{\mathrm{reference}}(S)
\]

其中 S 是同一工具链、相同定义环境、相同注册对象、相同 arena 分组、相同 primitive bundle 的当前快照。数学部分须有 Lean 等价证明；文件、缓存、流程部分须有集成测试与故障注入。不把测试称为形式证明。

### 0.1 本方案不采用的“优化”

不将 `∀ i, δᵢ > 0` 改成“只有某个挑选后的子集需要正增益”；不把同一 arena 拆成几个互不比较的组；不排除导致零增益的定理；不删除 primitive 来加速；不加人工权重、评分或新的测试域；不将 `axiom`、哈希收据或 `native_decide` 当成大证明的替代品。

上一轮讨论的“把不可约性仅施加于精简视图”属于语义政策调整，不纳入本工程方案。物理归档可以保留旧快照；当前注册族的判定仍然完全按现行规则执行。

### 0.2 一次编译的准确合同

冷工作树仍从现有 `make lean` / cache-writer 入口进入，不能先裸跑 Lake 破坏 donor 初始化条件。一个顶层构建调用中，Lake 可以按 DAG 编译多个文件、复用已有产物，`#seal_information_theory` 在 elaboration 内生成并检查伴随声明。禁止“先外部生成证明源码，再启动第二轮编译完成证明”的新链条。

缓存依赖过往计算，不等于把历史版本引入信息增益的数学定义。性能对照版本与 Git 治理 protected-base 也不等于数学 baseline，三者必须分别命名。

---

## 1. 当前源码事实与优化落点

| 已核对路径 | 当前行为 | 结论 |
|---|---|---|
| `lakefile.toml` | 默认目标包含 `Trureturing`、`LeanInformationAudit`，管理 `D5.+` | 优化不能简单删默认覆盖；先保持全覆盖、做增量复用 |
| `Makefile` | 已有 `make lean`、`lean-report`、`preflight`、`gate`、发布与取回缓存入口 | 扩展现有入口，不叠加第二套命令体系 |
| `tools/lean-inspector/Inspector.lean` | 一次 `importModules` 导入输入模块；积累 `reports` 后拼接 JSON | 需要批处理与流式编码，当前选择可能仍有很大的导入闭包 |
| 同上 | 公理闭包已有 Tarjan SCC 与运行级共享缓存 | 保留；不能将“新增 memoization”当作本轮主要收益 |
| `inspect.sh` / `delta.py` | 已有内容寻址、增量选择与未变记录复用 | 补全依赖证明和失败回退，不重写一个替代系统 |
| `delta.py` | `read_bytes` / `read_text` / `json.loads` 可形成多份报告内存表示 | 流式解析、按模块对象索引，逐步避免全报告驻留 |
| `CatalogBuilder.lean` | 按 `arenaName` 分组、确定顺序、构造当前目录 | arena 是语义边界，不是可以任意改的小批次 |
| `ProofBuilder.lean` | 逐定理计算 unique / without / 角色直方图，再构造全体正性证明 | 优先合并计数并消除重复证明求值 |
| `ExactRate.lean` | 已证明 `escapeNumerator_without_eq` 等式及正增益刻画 | 可直接复用，避免重新枚举每个留一族 |
| `SealCommand.lean` | 先在局部环境 kernel-check，再一次发布环境；JSON 为输出 | 保留原子性，增强文件发布与编译产物绑定 |
| `README.md`、缓存归属文档 | 私有工作树、禁止 symlink 共享 `.lake`、已有 clonefile/donor | 不以移除互斥锁或共享可写目录换性能 |
| `.github/workflows/ci.yml` | 缓存 restore 步骤中有失败会阻断 required job 的路径 | 单独处理可选缓存传输失败；真正检查失败仍阻断 |
| `docs/reports/lean-cache-ownership.md` | 明确承认缺少真实 Lake 缺失 olean 修复测试 | P0 必须补真实集成测试，不用 fake runner 结果代替 |

上述为源码审查，不是耗时排行。必须先测量各阶段 wall time、CPU、RSS、读写与锁等待，再决定并行度和批量大小。源码显示重复工作，不自动证明它是部署环境的最大耗时。

---

## 2. 目标架构与职责

```text
Source snapshot + exact toolchain + dependency lock
                    |
           Existing cache-writer boundary
                    |
               One Lake build
             /        |        \
       math modules  IE modules  library adapters
             \        |        /
          typed counts + proof certificates
                    |
          #seal_information_theory
          kernel-checked declarations
                    |
             checked build products
                    |
       batched Lean inspection / reports
                    |
    exact catalog coverage + canonical merge
                    |
        StrataLint governance / admission
                    |
        Scribe / Blueprint / truth release
```

**数学真源：** Lean 定义与 kernel 接受的证明项。  
**叙述真源：** 现有 Scribe 定义；Markdown、站点、搜索索引是投影。  
**治理：** 现有 StrataLint 路由、冻结、覆盖、依赖与来源规则。  
**缓存：** 可删除且可重建的加速材料，不决定真伪。  
**档案：** 可追溯的源码、依赖 pin、证明与发行材料，按现有追加纪律保留。

不得把多个层次压成一个 `valid: true`。内部状态至少区分：数学检查通过、当前信息封印通过、治理准入通过、产物来源已核对、资源阻塞、尚未检查。公开展示可以沿用现有 schema，但不能误报。

---

## 3. 四种依赖图必须分开

### 3.1 构建图 G_build

节点为模块与 Lake facet；边来自 Lean imports、插件、代码生成和显式构建依赖。谁需要重编译，由 Lake 与真实输入决定。不能仅凭“定理陈述没变”复用本该失效的环境。

### 3.2 证明审计图 G_proof

包括声明的类型、证明体、定义体、构造器、归纳类型及公理闭包依赖。允许声明级相互递归，因此 SCC 处理不可删。不能用只扫描定理正文中的显式名字替代完整依赖收集。

### 3.3 信息目录图 G_information

节点包括 registry entry、theorem unit、arena、primitive bundle、其所有真实定义依赖、排序及完整目录。一个同 arena 新成员可能改变所有旧成员的留一增益；必须使相应目录证书失效。不同 arena 的局部结果可复用，但全局注册覆盖根仍要更新。

### 3.4 叙述与发布图 G_document

节点包括 GID、Scribe AST、声明投影、覆盖边、页面与目录。Lean 陈述未变、只改叙述时，不必重复检查数学；但必须重新生成受影响叙述与覆盖产物。

统一目录提供关联，不把这四张图强行当成同一张失效图。各图的删除、重命名、依赖增加都纳入回归测试。

---

## 4. P0：可观测性与语义对照

扩展现有 `resource-observation-lib.sh` 及测试入口，避免额外常驻监控服务。

每次运行记录：snapshot、toolchain identity、host/platform、执行器身份、冷/热缓存、目标集合、编译模块数、缓存命中与验证失败数、每批导入闭包字节、阶段 wall/CPU、峰值 RSS、锁等待、spool 字节、报告字节、物理与表观缓存占用、退出原因。

把总时间拆成：

\[
T=T_{\rm provision}+T_{\rm build}+T_{\rm seal}
 +T_{\rm import}+T_{\rm inspect}+T_{\rm serialize}
 +T_{\rm governance}+T_{\rm scribe}.
\]

固定工作负载包括：无修改热运行、小叶子证明变更、基础定义变更、同 arena 新成员、删模块、只改叙述、工具链变更、重型外部库、缓存失联、缓存损坏。

**对照口径：** 字节对照指同一候选源码、同一编译产物，由 reference Inspector 与 optimized Inspector 分别生成的 canonical payload。不是要求不同提交、不同 source hash 或合法新增声明的报告仍然相同。producer 身份和性能记录应置于各自来源信封，不混入旧 payload 的字节比较。数学算法对照则针对同一目录与 primitive 输入。

**P0 硬验收：** 在上述相同输入口径下，原始规范报告字段/顺序/字节和准入结果不变；所有已要求检查继续执行或由合法、匹配输入的产物覆盖；不允许以 skipped 充当 passed。

资源数据可指导工程调度，不能输入数学增益或成为新的数学价值阈值。

---

## 5. Inspector 分批与流式处理

### 5.1 输入改为 manifest，而非无限增长的 argv

为 `Inspector.lean` 增加兼容的 `--module-manifest` 入口。清单包含精确 module、source path、source hash；拒绝重复名字、路径逃逸和不存在文件。原 triples 入口保留到迁移结束。

清单由当前快照枚举器生成，不从用户选择的子集冒充全局目录。批处理器可以重排工作，但最终集合必须与枚举集合完全相同。

### 5.2 批次按闭包成本形成

先从 Lake 的实际依赖和产物大小估算每个模块闭包，再将共享依赖多的模块分在同批。不能只按“每批 100 文件”切分：100 个小模块可能导入同一个巨型库。

每个 worker 只加载本批所需环境，保留其运行内 SCC 公理缓存；输出仅限本批拥有的模块，导入依赖不重复输出为新的受管模块。worker 结束后由操作系统回收完整进程内存。

同一批的公理集合要与 stock `Lean.collectAxioms` 抽样及专项循环模型对照。不同环境之间不得仅按声明名字共享 axiom closure。

### 5.3 每个声明仍使用原规范编码

保持 `encodeName`、`encodeLevel`、`encodeExpr`、`includeInStatement` 的语义与现有 statement ID。不靠打印出来相同就合并定义；不靠图同构推断数学等价。

第一步将拼接大字符串改成字节等价的增量写入，或按声明分块编码后拼接。需要测试 UTF-8 字节长度、非 BMP 字符、private name、universe、定义体、元数据与转义。不要同时变更编码规范和性能实现。

### 5.4 报告合并

worker 输出可用内部模块分片。最终 writer 以模块名、声明名的现有规范顺序合并。验证：

\[
\text{emitted modules}=\text{expected modules}
\]

且每个模块恰好一次；不存在重复、遗漏、旧 source hash。序列化格式保持 canonical v2，内部存储变化不自动升级公开协议。

`delta.py` 中旧报告复用改为模块偏移索引与流式复制，避免整份 bytes、Unicode text、JSON DOM、raw substring 多重驻留。输出材料归档也使用流式读取；归档路径、时间戳和排序保持现有规范。

### 5.5 不能承诺任意小内存

批处理降低多个闭包同时驻留的成本，但单个模块的巨大闭包仍可能超预算。此时需要拆分源模块、采用公开/私有模块或使用重资源 runner，不能悄悄跳过这个模块。

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

### 6.4 通用正确性定理

拟议新文件置于既有命名空间，不重新定义 `Arena`、`Catalog` 或 `PrimitiveBundle`：

```text
D5/S3/ConceptDynamics/InformationEscape/Counting/
  Fused.lean
  FusedCorrectness.lean
  Partition.lean
  PartitionCorrectness.lean
  RoleHistogram.lean
  BlockComposition.lean
```

每项通过当前 GID、Blueprint/Scribe、依赖、冻结流程准入。不要以优化项目为由跳过治理要求。

需要的核心结论：fused full 等于 `escapeNumerator full`；fused unique 等于 `uniqueCaptureCount`；histogram 等于现有筛选计数；partition 与 fused 相等；disjoint blocks 合成精确覆盖全集。

---

## 7. 分块计算不等于缩小比较范围

同一 arena 可以按状态对域分块：例如第 k 块负责一段左状态序号及全部右状态。每块必须比较**完整 m 条定理**。

块输出：

\[
(C^{(k)},U^{(k)}_0,...,U^{(k)}_{m-1},H^{(k)}).
\]

在块互不重叠、并集精确等于非对角对域的前提下，合计得到全量向量。

不能分成“模块 A 里的定理互相比一次，模块 B 里的定理互相比一次”再各自声称正增益。两个完全重复的读出分处不同源文件，也必须在全局 arena 得到 U=0 并拒绝。

每个块的正确性证明绑定完整目录对象和 arena，不只绑定一个脱离语义的 JSON 哈希。跨进程调度传递对象地址，但最终 Lean 证明必须通过实际类型、目录及覆盖定理组合。

---

## 8. ProofBuilder：共享已检查结果，不重复展开同一大计算

保留原定义作为 reference semantics。新加的辅助计数证明不自动注册为新的 theorem unit；否则会改变待评估目录，已经不属于同输入优化。在 elaboration 中准备一个类型化 Counts 对象，并构造其等于 reference counts 的正确性证明。

建议内部结构语义如下（不是已编译 API）：

```text
CertifiedCounts(catalog):
  full : Nat
  unique : Index -> Nat
  without : Index -> Nat
  roleBins : Index -> RoleMask -> Nat
  full_correct
  unique_correct
  without_correct
  roleBins_correct
```

先证明一次向量/块结果正确，再从小数值的正性及 `unique_correct` 导出原类型的 `__lowers_escape`。保留原声明名与对外命题类型。

全体 `__catalog_irredundant` 由已检查的逐项证明按有限索引构造，不再通过一个新的 `decidableForall` 重新计算所有 `uniqueCaptureCount`。

不得只用 metaprogram 求得 n，再直接构造 `0<n` 而没有 n 与 reference count 的证明。不得用 kernel 不检查的 native 结果替换证明。元程序可以不可信地搜索或建议证书；接受的 proof term 必须能通过普通 kernel 检查。

注意：一个体积小的 `by decide` 可能导致很重的 kernel reduction；一个编译执行很快的计数函数也不意味着其相等证明检查很快。分别测量 evaluation、proof construction、kernel check、proof bytes。

JSON 中方法名必须真实反映执行路线。若 provenance 字段变化，使用旁文件或经过批准的 schema 迁移，不能为了字节对照把新方法伪装成旧方法。

---

## 9. 封印、快照覆盖与发布原子性

现有 `SealCommand.lean` 先准备、预检名字，再 `addDeclCore` 检查，最后一次 `setEnv`。保留这种事务式环境发布。

增加三个检查：

1. 当前 seal 预期处理的 registry entries 与实际条目完全一致。
2. 每个目录证书绑定成员集合、确定顺序、arena、primitive 与依赖环境。
3. 旧快照证书不因原始数学命题未变而被错误复用到新目录。

一个源文件只看见所导入的 registry entries，不能仅靠局部环境就声称“已经看见仓库全部注册项”。项目级覆盖清单必须来自确定的源快照与已有枚举器，并验证完整集合。该清单证明工程覆盖，不冒充“枚举了数学世界所有定理”。

区分两种原子域：

- Lean 环境：全部新声明检查成功后才替换环境。
- 文件发行：`.olean` 等构建产物生成完成、JSON/材料及 checksum 校验完成后，才发布最终 manifest/COMMITTED 标记。

输出先写唯一 staging 目录；原子 rename 发布。不能只因为 `#seal` 写出了 JSON 就认定整个 Lean 编译已经成功，因为后续编译可能失败。最终发布目标依赖已完成的构建 facets，读者只认完成标记。崩溃留下的 pending 文件永不准入。

---

## 10. 模块与公开接口迁移

短期不移动全部 `D5` 路径，避免破坏 GID、frozen identity、Scribe 引用和既有 imports。

从一个依赖封闭的小领域做试点，区分：公共定义/定理接口、仅供证明的实现、元程序与测试。保持原文件作为兼容入口直到完整迁移与审计通过。

Lean 官方模块系统支持公开/私有作用域与不导入私有证明信息。但“隐藏实现”只保证相应边界下的可见性与加载行为，不保证自动压缩成独立小证书。公开声明的类型若引用大量领域定义，公共依赖仍然可能很大。

试点验收：消费模块通过；必要 definitional equality 不丢失；simp/instance/notation/extension registry 行为正确；原完整公理闭包仍可审计；只改私有证明时的实际重编译范围下降；公开 interface 包没有携带可删的大证明体；完整审计包仍可独立检查。

不能为隐藏证明而让 Inspector 看到“缺失证明体”就当作无公理。审计端应使用该版本支持的完整私有环境/导出路径；消费端才使用轻接口。当前 pin 的具体 API 和 artifact 切分必须实测，不能把 `latest` 文档直接当成安装版本的行为承诺。

---

## 11. 重型外部库适配

为 FLT 等设置独立的锁定构建单元。记录源 commit、Lean/Mathlib exact pin、补丁、许可证、公开定理陈述、定义对应、完整公理闭包、构建与重放收据。

先有契约明确的适配器，再引入真实证明。轻核心可以证明 `FLT -> Q`；只有同一兼容 Lean 环境中接入实际 `p : FLT`，才能交付无条件 Q。跨不兼容 toolchain 的 JSON 证书不能直接当成 Lean 证明。

工具链不一致时，选择协调到经过验证的共同版本，或暂时保留隔离结果而不冒充已链接。不要让依赖解析器悄悄用上游库自己的 Mathlib 替换主库定义。

测三条路径：从源码构建、只导入并使用一次、完整独立重放。三者资源数据不能互相替代。未测量前，不承诺任何轻接口的 MB 数值。

---

## 12. 缓存：语义不变、来源明确、失效完整

### 12.1 分层

- 工具链/依赖缓存：固定 compiler 与 package 版本。
- Lake 模块产物缓存：按真实构建输入复用。
- Inspector 模块记录缓存：完整输入环境、producer 和 schema 相同才复用。
- IE 目录/块证书缓存：同一精确目录和语义输入才复用。
- Scribe 产物缓存：声明投影、Scribe AST、模板/工具版本相同才复用。

数学对象的 SHA-256 地址只用于寻址；kernel 决定的相等关系不能由“SHA 相同”替代。

### 12.2 补充来源信封，不替换现有 statement ID

拟议 envelope：

```json
{
  "schema": "trureturing-artifact-envelope-v1",
  "artifact_kind": "inspector-module-record",
  "logical_id": "existing-GID-or-module",
  "source_digest": "sha256:<64-hex>",
  "toolchain_digest": "sha256:<64-hex>",
  "dependency_lock_digest": "sha256:<64-hex>",
  "dependency_artifact_root": "sha256:<64-hex>",
  "producer_digest": "sha256:<64-hex>",
  "options_digest": "sha256:<64-hex>",
  "platform": "exact-target",
  "payload_digest": "sha256:<64-hex>",
  "verification_record": "immutable-record-id"
}
```

这是传输/构建协议，不是数学证明类型。旧原文、statement ID、GID 不回写。实际 key 还应包含插件、影响构建的环境设置和经声明的外部输入；缺失输入不能靠加一个 Git SHA 掩盖。

### 12.3 信任与威胁边界

哈希证明收到的字节与某个摘要匹配，不证明字节是谁构建的、更不证明数学正确。共享缓存只允许受控构建端发布；候选任务没有正式缓存写权限。已签名清单也只证明来源，不等于 kernel proof。

导入产物可伴随执行插件/元程序，未知来源 cache 必须先在隔离、无敏感凭据环境核对或重建，不能先加载再验证来源。

Lake 现有 trace 与缓存机制负责加速和构建失效，不取代项目的密码学来源绑定。官方仍将部分 artifact cache 能力标为实验性，且可能改变产物位置；不要直接全局开启，再让现有硬编码路径失效。先在小范围兼容试点验证后决定复用路径。

### 12.4 不同失败的处理

缓存未命中/可选服务不可达：沿既有有权限、有预算的源码重建路径继续；环境不允许冷构建则记录资源/基础设施阻塞。

摘要不匹配、producer 不匹配、目录错位：隔离该缓存，禁止使用；只有从可信源重新产生并通过检查后才能继续。

symlink 拒绝、写锁冲突、目标目录损坏、校验失败：保持现有阻断，不以 `continue-on-error` 包掉。

证明失败或准入失败：直接失败，绝不回退旧结果。

---

## 13. 工作树、磁盘与生命周期

保持每棵工作树私有可写 `.lake`。已有 APFS clonefile 优先路径继续使用；其它文件系统的 copy-on-write/reflink 只能作为经过隔离验证的优化。禁止 symlink 共享可写缓存，禁止给可写构建文件建跨工作树 hardlink。

进程内调度锁与跨进程文件互斥应区分。构建阶段持写租约；检查阶段可在构建完成后使用经过测试的只读租约，共享不可变快照但不再触发构建。不得删除现有 writer guard 来获得并行。

将长期档案与可丢弃缓存分开：源码、固定依赖来源、正式收据、可恢复的完整证明材料属于档案；spool、临时报告、已失效工作缓存属于可清理对象。已有 Git/ledger 追加规则保持，不能重写历史或先删除 canonical 数据再声称迁移成功。

清理依赖 manifest 图执行 mark-and-sweep：根包括当前快照、保留发行、冻结记录、活动租约、审计 pin；先列计划，再测试恢复，再删除明确无引用的临时对象。并发 GC 不能删除正在导入的文件。

C、object、`.olean`、私有模块数据、语言服务器数据不能一概删除：发布消费包、开发包、审计包、运行插件包分别给出精确所需 facet 清单。若要预先不生成某类产物，须验证不影响后续编译期执行与当前默认目标。

同一工具链下去重不消除多平台、多版本的真实成本。物理空间按平台/版本与保留策略核算，不使用文件表观大小冒充 APFS 物理占用。

---

## 14. 资源调度

先复用 Lake 的 DAG，不重新实现一套构建系统。对 Inspector 和重型独立集成任务增加外层资源预算；未来确有需要时，再研究如何在不破坏 Lake trace 的情况下限制构建并发。

工作集约束：

\[
\sum_{j\in\mathrm{running}}\widehat M_j
\le M_{\mathrm{available}}-M_{\mathrm{reserve}}.
\]

`widehat M` 来自同类任务的观测及保守裕量，不是数学评分。没有数据的新模块按保守类别运行并采样更新。

同时限制任务进程数与单进程线程数，避免“外层并行×内层线程”超订阅。单模块超过机器预算时排到重资源环境，或返回清楚的资源阻塞，不报告数学反例。

独立节点只收到确切任务清单；返回的产物必须绑定输入、编译器和检查记录。需要重新检查时支付真实成本，不能把分布式执行当成免验证。

---

## 15. CI 与单次构建整合

保留现有 required check 名称、merge-result 输入和 protected-base 治理逻辑。数学 no-baseline 不要求删除 Git 治理基线。

为可选 cache restore 网络/服务错误设置受控回退，但必须：捕获具体错误、隔离不完整目录、重新验证或重建、保持最终 Lean 和治理检查必需。不得对整项 Lean job 或 admission 使用忽略错误。

`inspect.sh` 当前负责一次 `lake build` 后再执行报告程序。第一阶段保留这个入口，只拆检查批次，不额外从 worker 反复调用 `lake build`。数学封印仍在该构建中完成；报告程序只是读取已编译结果。

若需要让一条 Lake target 统一管理封印与投影产物，在成熟阶段通过自定义 facet 配置；TOML 迁移到 `lakefile.lean` 必须单独提交，证明依赖、默认覆盖和目标行为一致，不能并存两个配置真源。元程序创建声明留在同次 elaboration 内，禁止外部先生成证明 Lean 源码再重编。

发行按构建、数学检查、治理检查、Scribe、来源验证、原子 manifest 发布的依赖顺序执行。任何阶段失败，不生成当前快照的正式发布记录。

---

## 16. 身份、模型和全局注册风险

三个不同的 ID 不能合并：

- 稳定逻辑地址：现有 GID、声明名称等，承载用户引用。
- 陈述/定义身份：现有 canonical 编码与依赖语义。
- 构建产物身份：工具链、选项、平台、源码与依赖产物共同确定。

同名不保证同义；定理类型摘要相同但所引用定义变了，也不能复用旧语义审计。发布清单必须能追踪定义环境。

增量扫描必须包括删除与重命名：旧图定位反向依赖，新源码提取新边。删除的模块不再是检查输入，但仍导入它的存活模块必须失败或修复。

registry 的持久化扩展与公开/私有模块迁移也要测试。不能因为某个 extension 没被导入而少看几条定理，使原本失败的目录通过。

---

## 17. 形式化不变量清单

拟议定理要求如下，确切命名先通过仓库查重：

| 不变量 | 应证明内容 |
|---|---|
| 融合扫描正确 | full、unique、without 与 reference 定义逐项相等 |
| histogram 完备 | 15 类 bins 各自准确，和为 unique |
| 分区正确 | 类标签相等当且仅当目标 kernel 同意 |
| 留一标签正确 | prefix/suffix pair 等价于删除该坐标后的联合读出 |
| 分块正确 | 块互斥且覆盖完整对域，计数可相加 |
| 证书组合正确 | 最终原声明类型不变，所有数值都绑定真实目录 |
| 判定保持 | 相同完整输入下接受/拒绝完全等价 |
| 目录更新正确 | 新成员不被旧快照证书覆盖 |
| 非退化前件保持 | 空或单态域仍按照现有规则拒绝 |

工程不变量另由集成测试验证：精确模块覆盖、字节稳定、输入哈希完备、缓存失效、原子发布、锁隔离、来源权限。不能把这些工程测试笼统称作 Lean 已证明。

---

## 18. 测试矩阵

| 测试 | 预期结果 |
|---|---|
| 无修改热树重复构建 | 不新增无谓 Lean 编译；报告和声明投影不漂移 |
| 小叶子证明变化 | 必要证明审计更新；不加载不相关领域 |
| 公共定义或插件变化 | 真实依赖闭包失效，不只看定理文字 |
| 同 arena 加入重复读出 | 原 positive 可能变零；当前封印必须拒绝 |
| 将重复读出分到不同 worker | 仍然拒绝，不能各自局部通过 |
| 只改 ANCHOR / ADMIT / FLOW | 与当前语义一致地改变计算或保持；不凭标签猜测 |
| 空 bundle、退化 arena | 原错误规则继续生效 |
| 删模块、改 imports、重命名 | 不复用不再存在环境的旧记录 |
| 工具链、Mathlib pin、options 改动 | 跨版本 cache 不被误认兼容 |
| 强制造哈希冲突的索引实现 | 碰撞桶中精确比较；数学结果不变 |
| 伪造 JSON 成功标志 | 不产生 proof，不取得正式准入 |
| 丢失/重复 registry entry 或 batch | 精确覆盖校验失败 |
| cache 网络不可达 | 合法重建或清楚的资源阻塞，不虚假失败为数学错误 |
| cache artifact 损坏 | 隔离并重新产生；不导入坏字节 |
| 真删除一个必要 Mathlib olean | 在隔离副本实际运行当前 pin 的 Lake，观察恢复或真实错误 |
| 两工作树并发写入与 GC | 无交叉修改，无租约中对象被回收 |
| kill worker / kill during publish | 不存在半份正式 manifest 或成功报告 |
| private proof 迁移 | 下游可用，完整审计仍含正确公理闭包 |
| unsafe/native 路径意外进入 proof | 既有公理与来源策略拒绝或明确告警，不静默放宽 |
| Scribe-only 编辑 | 叙述重新发射，数学无需伪重建 |

**方案形成时的原型测试记录（原型不属于本次文档 PR）：** `counting_reference.py` 对 3,784 个穷举模型及 600 个固定种子的随机模型比较 literal、fused、partition 三条路线，并检查所有角色直方图、分块可加性和跨分片重复读出拒绝。共 4,384 个模型全部一致。测试输入直接提供精确角色标签，不能据此声称实际 Lean primitive 标签构造无成本；这也不是仓库运行性能基准或 Lean 证明。

---

## 19. 容量边界：优化不改变数学上限

对一个固定 N 状态的有限 arena，如果 m 条读出都拥有独有捕获见证，则 m≤N−1。因为无论以何顺序加入，每条都必须严格细分先前分区，而分区从一类最多增加到 N 类。

这是不可约读出族的限制，不是数学证明总数的限制。在“不改准入规则”约束下，工程不能让同一固定 arena 中任意多的读出全部正增益。重复或被替代的读出仍会被拒绝。不得通过追加无语义标签、任选更大状态域或任意切分 arena 规避。

全库可以有多个已有、语义明确的 arena；优化复用各自结果，不强制把所有领域投进一个笛卡尔积，也不自动为提分而创建新 arena。新模型属于数学建模工作，应走原准入流程。

---

## 20. 分阶段实施包

| 包 | 修改范围 | 交付物 | 放行标准 |
|---|---|---|---|
| P0-Observe | 现有资源记录、缓存集成测试 | 固定 workload、阶段账本、真实缺失 olean 测试 | 不变更报告语义/准入 |
| P0-CacheFailure | CI cache restore 和既有恢复路径 | 分类错误与可信回退测试 | cache 失败不冒充数学失败；坏缓存不被使用 |
| P1-Counts | `ExactRate` 的使用、Counting 新定理 | fused 算法及 Lean 正确性证明 | reference 全字段相等 |
| P1-Proofs | `ProofBuilder`、`SealCommand` | 共享计数证书与全体正性组合 | 同名同型、无新增不允许公理、原子发布 |
| P1-Inspect | Inspector、delta、materials | manifest 输入、分批 worker、流式 writer | 原 canonical 报告字节相同、覆盖完全 |
| P2-Partitions | finite label / prefix/suffix / role bins | 高效索引与正确性桥 | 包含标签构造的端到端收益为正 |
| P2-Modules | 小领域 module 试点 | 接口/实现边界与完整审计路径 | 实测减少导入或重编译，无语义缺口 |
| P2-Artifacts | 既有发布缓存扩展 | envelope、模块对象存储、恢复与 GC | 冷路径仍可独立产生，历史可恢复 |
| P3-Heavy | FLT 等独立适配目标 | pin、接口、桥接、三类资源报告 | 实际 proof 已链接、无跨环境偷换 |
| P3-Scale | 现有工具上的资源调度 | 有界 workers、只读租约、恢复演练 | 不漏模块、不弱化准入、资源曲线可解释 |

每个包独立 PR，保留可回滚点；不把模块迁移、数学算法替换、report schema、工具链升级同时塞进一个 PR。新算法失败时可退回原算法，只允许执行策略回滚，不允许回滚当前快照的数据来换取通过。

---

## 21. 建议文件职责映射

| 现有文件/目录 | 修改建议 |
|---|---|
| `tools/lean-inspector/Inspector.lean` | 保留 SCC；增加 manifest、逐模块写出和批次消费 |
| `tools/lean-inspector/inspect.sh` | 一次 build 后批次执行；增加只读检查边界；不循环启动 build |
| `tools/lean-inspector/delta.py` | 保留旧记录复用语义；流式解析与完整失效测试 |
| `tools/lean-inspector/materials.py` | bounded-memory 编码/归档，不改 statement bytes |
| `tools/lean-inspector/LeanInformationAudit/ProofBuilder.lean` | 调用经证明 fused/partition 结果；共享 proof |
| `.../CatalogBuilder.lean` | 完整 registry 与 arena 顺序不变；新增快照/目录绑定 |
| `.../SealCommand.lean` | 现有环境事务不变；候选产物与最终发布分离 |
| `D5/.../InformationEscape/Counting/` | 新算法、等价、块合成定理；按现有流程配置镜像与 Scribe |
| `tools/StrataLint.Cli/Commands/Worktrees/` | 租约、缓存 envelope、恢复；不取消私有目录策略 |
| `tools/StrataLint.Engine/` | 消费确定报告、保持治理规则；不重算数学分数 |
| `tools/StrataLint.Scribe/` | 读取同一快照投影，按受影响 GID 生成 |
| `tools/tests/` 与现有 Lean 测试目录 | 字节对照、故障注入、算法等价与真实 Lake 集成 |
| `.github/workflows/ci.yml` | 仅改变执行与缓存恢复，required verdict 合同保留 |
| `Makefile` | 仍只路由，不塞逻辑 |

初期不新增集中式数据库或常驻服务。需要快速索引时先用可重建的本地索引和模块对象目录，测到瓶颈后再扩展。源存档与索引不是两个数学真源。

---

## 22. 回滚与验收

### 数学放行

相同输入下，完整 registered catalog、各 arena、full/without/unique/role bins、正增益 verdict、公开证书命题全部等价。原本拒绝的重复目录继续拒绝。没有不允许的新公理或隐藏前提。

### 工程放行

原 canonical 记录不变；所有 expected module 均有且仅有一份结果；缓存丢失仍存在可信构建路径；坏缓存不能通过；工作树无互写；发布没有半成品；源码和正式收据历史保持。

### 性能放行

用相同快照、硬件、缓存条件比较。记录热/冷情况而不是混算。无改动时数学模块重编数为零；小更新的工作范围可由真实依赖解释；Inspector 峰值由批次闭包而非全库选择决定；计数不再为每个 i 重建所有留一对集合。具体秒数、GB 和倍数以实测为准，不承诺尚未得到的数值。

内存下降但总时间明显恶化的批次策略不能默认全库启用，应调整闭包聚类和并行度。任何优化需要超出当前可用资源时，给出明确 blocked，而不是 fabricated proof 或错误的 zero capture。

### 退回规则

分片报告不一致：退回原 Inspector。算法等价或 kernel check 未完成：继续 reference 算法。公开模块迁移丢失审计信息：保持普通导入。缓存服务异常：走原许可重建路径。所有退回均记录原因，不静默改变快照。

---

## 23. 审查来源

下列仓库路径均读取自本方案顶部固定提交；路径足以在该快照复核。网络说明使用官方文档，具体特性落地前仍以项目 pin 的真实编译结果为准。

[S1] `README.md`、`Makefile`、`lakefile.toml`。  
[S2] `tools/lean-inspector/Inspector.lean`。  
[S3] `tools/lean-inspector/inspect.sh`、`delta.py`。  
[S4] `tools/lean-inspector/LeanInformationAudit/CatalogBuilder.lean`。  
[S5] `tools/lean-inspector/LeanInformationAudit/ProofBuilder.lean`。  
[S6] `tools/lean-inspector/LeanInformationAudit/SealCommand.lean`。  
[S7] `D5/S3/ConceptDynamics/InformationEscape/ExactRate.lean`。  
[S8] `docs/develop/spec/lean_single_compile_intrinsic_information_escape_theory_and_spec.md`。  
[S9] `docs/reports/lean-cache-ownership.md`。  
[S10] `.github/workflows/ci.yml`。  
[S11] Lean 官方《Source Files and Modules》：`https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/`。  
[S12] Lean 官方《Lake》：`https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/`。  
[S13] Lean 官方《Validating a Lean Proof》：`https://lean-lang.org/doc/reference/latest/ValidatingProofs/`。

仓库快照入口：`https://github.com/the-omega-institute/trureturing/tree/d0e63dda80290fc39bfc46fe8310b4b47a661e28`。

## 24. 最终实施顺序

先测量并补缓存真实恢复测试；随后复用既有计数恒等式、做一次融合统计和证明共享；并行推进 Inspector 分批与流式输出；取得实际收益后，才做公开/私有模块迁移、细粒度产物发布和 FLT 等重型依赖适配。

最终目标不是宣称全人类逻辑可以装入固定内存，而是使**完整档案持续增长，而每次构建、检查与推理尽量只支付真实相关的增量成本，并始终保留相同的数学与治理保证**。
