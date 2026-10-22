# 搜索约化逃逸审计契约

## 1. 目的与边界

本契约观察一个已交付、经 Lean kernel 接受的证明的声明依赖链，判断加入具名辅助结构 `S` 后，沿该路线到达原目标 `T` 所需的辅助构造层数是否减少。约化量为 `Δ = d_B(T) − d_{B∪S}(T)`。构造包括选出中间陈述或见证；给定一个陈述后能例行证明它，不等于选出这个陈述是免费的。

结果永远是 `Observe`，不产生 Block、总分、权重或新的准入状态。依赖提取、局部重建、距离和判词由 Lean 计算，成功证书由 kernel 复核；JSON 只是投影，不读回作语义判断。旧结算保持原有基底、配置和结论。

“更容易”只指登记的声明图、局部重建者和预算内的读数，不是绝对证明难度、原搜索问题的复杂度或 P/NP 证书。作者路线可能遗漏更短证明；两臂各自的上界不能相减成为全局搜索收益的下界。局部过程按序执行也不推出多项式时间。

## 2. 登记、基底和共同环境

校准前固定原任务 `T`、交付批次、候选 `S`、声明图提取配置、`R_lookup` 的允许表与顺序、预算、工具链、词汇传输配置及窗口 `k=2`。每条读数带 `[G, R_lookup, k, B_used]` 及配置身份。不得为受益声明调整允许表、顺序或预算。

`T` 和声明类型保留完整 telescope、局部假设、宇宙、量词与依赖关系。`B0` 是受保护提交、钉版依赖及冻结 D5 的规范清单，只排除目标交付及其污染闭包；仅被交付导入的既有前置不排除。Lean 生成清单，并核验实际载入清单 `B_load ⊆ B0`。读数报告载入清单、`|B_load|/|B0|` 和模块 scope；作者 imports 不定义规范基底。

图的基底叶子 `B_used` 是活依赖实际用到且通过隔离核验的受保护常量，满足 `B_used ⊆ B_load`。图上负读数只属于 `B_used` 作用域，不上传为全 `B0` 的搜索结论。合规的 bind-only 证明或单源呈现证书可以从子基底用于较大基底；有限耗尽加配对证书不能这样上传，也不证明增强后的重建者仍会找到或仍会失败。

两臂共用一份核验后的词汇和不可变基底导入。探针不获得作者证明体、作者属性、simp 表、批内实例注册、初始化器或全库索引。私有常量按 Lean `Name` AST 传输，包括数字段，不经文本名重建。缺片、隔离失败、不支持的形态、预算耗尽与故障均具名记为 `unknown/incomplete`，不等同正常耗尽。

### 2.1 词汇与实例

只传输表达 `T` 与登记 `S` 类型所需的词汇闭包，按已完成的干净前缀重建；两臂使用同一结果。归纳类型和结构按完整互归纳组交 kernel 重建，recursor、matcher、投影等生成物由钉版生成器从重建类型生成，不复制作者环境的注册状态。未支持的组或生成物具名记 incomplete，不按声明名设例外。

词汇定义体内的副证明在完整 telescope 与宇宙下经 kernel 和标准三公理闭包核验后复制，不另作证明子项义务搜索，不使用占位公理。若 `T` 通过词汇定义投影其证明字段取得目标证书，则报具名 `target_in_vocabulary_certificate` incomplete；不得让该证明字段成为配对收益的来源。词汇传输成功本身不是基底成功证书。

实例由隔离后的基底环境 `synthInstance` 合成，排除批内实例，不限于 `B_used` 叶子的所有者。合成失败或使用了不准许的批内实例时具名 incomplete，不读回作者实例作为答案。

## 3. 声明依赖图与辅助构造

### 3.1 顶点和活依赖

顶点是 `T`、其活依赖闭包内的同批具名 `theorem`、`def`、`instance`，以及基底叶子 `B_used`。理论消化 atom 或 CAS id 只作地址，不作图节点。不得按命题相同、源码行数、文件、private 属性或 atom 数量收费。

批内归纳类型、构造子与 recursor 属于共同重建的词汇；其类型依赖继续遍历并入消费者，不把这些类型生成物当作缺少证明体的辅助声明，也不把它们的证书当成免费事实。

消费者 `v` 的作者边取其编译值，先按 `CLAUDE.md` §3.2(iv) 作 ζ/β/ι 归约、删除死项及被投影丢弃的分量，再以 `getUsedConstants` 读取同批与基底常量。依赖读取复用声明级 `CompiledAxioms.declarationDependencyParts`、`CompiledEvidence`、`CompiledSourceOperands` 机制。仅 import、死 `have/show/let`、未用分量或在活路径外提及的辅助声明不形成有效依赖。

matcher、等式引理、`_proof_n` 等编译器生成常量用 Lean 自身的识别机制并入所属声明；其活依赖归入所有者，不新增作者构造层。无法识别所有者、缺少所需编译值或出现不能解释的循环时具名 incomplete。

声明体整体是一层不透明构造，记 `opaque`。证明体只为提取依赖被线性读取，不向局部重建者开放；不递归内联 helper，不展开 tactic 证书，不读取 InfoTree，不建立应用脊、matcher/IH 或证明子项图。内联 `have` 不拆节点；要让某条辅助线被配对看见，它必须是活路径上的具名声明。

### 3.2 解析与合成

对直接前提声明 `u` 与消费者 `v`，先打开各自的全部 telescope。若存在把 `u` 的每个 binder 单射改名为 `v` telescope 中同型变量的映射，且改名后的 `type(u)` 在 δ 展开批内定义后，与 `v` 打开后的某个 `Prop` 子项通过 reducible `isDefEq` 相等，则 `u` 对 `v` 为**解析前提**。依赖 binder 的类型也须在该映射下相容。

否则 `u` 为**合成前提**，即本契约观察的辅助线。非变量项实例化和重复变量实例化不属于单射改名，因而为合成；例如 `addition n n` 不能因 `addition` 本身例行可证而成为解析前提。合取一侧、iff 一侧、别名和在上述检验下匹配的条件拆分属于解析。匹配不完整或预算耗尽是 unknown，不是合成的否定证书。

受保护基底事实作为种子，其头的选择免费。合成前提是否进入种子集则改变可见信息：非种子合成前提的类型不给 `R_lookup`；已播种的合成前提可作为假设。这使选切式与给定切式后证明结论分开计价。

### 3.3 陈述级定价

基底臂种子 `X=B_used`，配对臂种子 `X=B_used∪S`。两臂使用同一张图、同一个定价函数和同一预算，只改变种子。所有局部探针只读声明陈述，不读其证明体。

对非种子消费者 `v`，`R_lookup` 只获得其种子前提与解析前提的类型作为假设：

- `c_X(v)=0`：探针闭合 `type(v)`，证明通过 kernel 复核。零价边保留证书**实际使用**的前提；其深度是所用解析前提深度的最大值，种子前提深度为零。
- `c_X(v)=1`：冻结允许表的全部尝试正常结束仍未闭合。作者边保留全部活的非种子前提，其深度为这些前提的最大深度加一。
- `unknown`：预算、故障、缺件或不完整读取；不得改记为一。

边的单位是辅助构造层，不是作者证明体中的原语数、数据实参个数或历史搜索回溯次数。一个局部 `rfl` 可证的具体等式仍能作为存在性目标的合成辅助线；选择该等式所携带的见证可有代价。

### 3.4 `R_lookup`：冻结闭合表与一步查表

闭合表按以下顺序冻结，旧局部闭合路线保留独立的 `200000` 搜索心跳预算。查表对每个候选独立分配 κ = `200000` 搜索心跳及 `8000000` 准备心跳。候选的全部视图、实例化、副条件闭合、证书组装与最终 kernel 核验共用 κ；每次候选尝试均从分支初态开始并重置 Core/Meta 缓存。视图遍历不设独立深度上限，全部工作计入 κ。候选超限记 capped；异常只使该候选 unknown，枚举继续。每个 unknown 报出模块、名字、原因及两份预算消耗，超过 κ 不属于正常失败。

搜索计入查询规范化、视图生成、实例化、合一、实例合成、闭合表义务、新证书构造与最终 kernel 核验。准备计入索引读取、olean 加载、签名与证明体的确定性词汇搬运和重建；这些物化操作不选择候选、不创建或赋值查询元变量。已认证 B0 的内联证明载荷不重复做中间 kernel 复核；重建计算声明的合法性及最终查询环境中的闭合证书仍经 kernel 检查。心跳均以 Lean 对外单位报告，内部读数为其 1000 倍。

每查询另有覆盖上界 G = `340000000` 心跳，计量候选搜索与准备之和。G 由判词无关的完整后备枚举底价及固定位置候选成本分布预先冻结，并写入 R 版本；它仅截断枚举，未访问部分为 unknown，不是语义难度上界。穷举否定的审计成本随 B0 增长，只作遥测。成功证书优先；NoHit 要求成员完整、主索引与后备完整、所有候选均在两份上限内正常失败且 capped 为空。G 增大只允许结算 unknown，不能推翻已认证结果。允许表、顺序、κ、准备上限和 G 不按读数调整。

1. `intro`；
2. `assumption`；
3. `rfl`；
4. And/Iff/Exists/Subtype 的结构引入与消去，数据只经合一确定；
5. 按固定顺序对单一直接前提 `apply`，其余目标用 `assumption` 闭合，不启用 `solve_by_elim` 的 symm、exfalso 或额外 constructor 搜索；
6. `simp only [直接等式/iff 前提]`，关闭环境 simproc；
7. `omega`，只用于无元变量目标；
8. `ring`、`ring_nf`；
9. `linarith only [直接前提]`；
10. `positivity`；
11. `norm_num1`；
12. 有界 `decide`，目标中不得含有限域量词。

排除 `nlinarith`、`polyrith`、`aesop`、完整 `solve_by_elim`、`exact?`、`apply?`、默认 `simp` 和 `tauto`。闭合过程只使用可见前提与冻结实例机制，不递归调用查表。新增查表路线只查询受保护基底 B，交付批内声明与 T 不入表。

对每个叶目标至多应用一条 B 声明，允许全称实例化、And/Subtype 投影、带证书的 Iff 方向与等式方向。数据参数只由目标、可见 Γ 的合一或冻结实例机制确定；剩余命题义务只交上述闭合表。不猜见证，不发明切式，不递归查表。成功证明项须经 kernel 复核且公理闭包包含于标准三公理。零价边只携带证书实际使用的可见前提；没有局部依赖的命中是零叶。

查表是二值关系，不使用频度、惊奇度或重复登记次数。完整陈述的成员查询以规范化 N 后、α 等价不变的完整陈述哈希为键；推论查询以规范化结论的判别树键路径为键，并包含 And 投影、Iff 方向与必要通配视图。键只负责召回，实例化、`isDefEq` 与 kernel 证书决定命中。变量改名、全称参数次序、投影、Iff 方向和实例的等价写法均须经过召回验收；未证明覆盖的键筛选不能支持 NoHit。

磁盘索引契约要求独立生产者按模块分片、分页写出，并对账受保护 B0 清单。索引按基底数据输入与显式版本号复用，不哈希程序字节。消费者只读取命中页及必要通配页，额外索引内存为 O(命中)，不对全环境建树，不调用 `exact?`、`apply?` 或 `LazyDiscrTree` 全库树。总内存仍包含 Lean 导入闭包；O(命中) 不是整个进程的内存界。

The current backend is `R_lookup/v10/candidate-200000/preparation-8000000/G-340000000/memo-off/N-memo-2000000/checkpoint-v1/external-64/native-signature/query-extensions/views-kappa/analytic-cut-k2/200000`. `make search-reduction-index INDEX_BASIS=<protected-commit> INDEX_DIR=<build-directory>` produces the index offline. Reuse depends on compiled basis data, the Mathlib pin, Lean version and explicit format versions. Implication candidates use Lean core `DiscrTree.mkPath` and `getMatch`, including projection and direction views; dropped `[*]` and `[Eq,*,*,*]` keys are separate fallback candidates. Batteries pickle/withUnpickle supplies module shards and mapped compacted storage. Candidate order is a stable partition with already loaded owners first, followed within each partition by module name and module-local declaration ordinal; fallback follows the primary route. This affects materialization order and never removes external B0 entries.

The preparation allocation is frozen from verdict-free, preparation-only cold-process telemetry. The sample includes every previously capped candidate identity, with four cold repeats per identity, and uncensored comparison candidates. A censored 4000000-heartbeat probe establishes a lower bound; it does not establish completion cost. R assigns 8000000 preparation heartbeats, using twice the largest sampled cost rounded to a whole million, with a censored sample contributing its probe limit. Candidates still exceeding this allocation remain unknown. The allocation stays fixed throughout calibration.

Exact membership has the independent format `R_lookup/membership-alpha-syntax-v3-memo-2000000`. Both producer and query normalize the complete statement, preserving its telescope, using the shared frozen syntax normalization from the presentation path, with beta/zeta preprocessing. Only noncomputational acyclic aliases unfold; recursive computations, matchers, recursors and instance dictionaries remain opaque. Metadata, binder names and binder annotations are removed; universe parameters receive canonical names in occurrence order. Alias-stack-sensitive memoization preserves N's result. Production and queries use the same fixed 2000000-node normalization fuel. The de Bruijn expression's core hash addresses one disk bucket containing a hash map. Only equal-hash entries undergo the existing definitional-equality and certificate checks; collisions never certify a proof. `make search-reduction-membership-index-run INDEX_DIR=<directory>` adds this sidecar to an existing complete implication index. The sidecar binds to that index's compiled-input fingerprint. Missing membership data, normalization failures and unreadable buckets cannot certify NoHit.

The semantic candidate scope is all protected B0, excluding the delivery batch, T and modules in the reverse import closure of T's owner. Imports and registered prerequisites affect materialization order only; they do not filter B0. Candidate identity is (module, Name). Separate candidate modules are never jointly imported to resolve conflicting owners.

The consumer never scans B or constructs an environment-wide index. Lean natively co-imports the baseline modules and one candidate module, preserving nested inductive groups, generated declarations and the original candidate signature. Query computational vocabulary is reconstructed into that environment. Persistent environment extensions are taken from the exact query environment, preserving its fixed instance and tactic tables while excluding candidate and author-source registrations. Author theorem bodies are not imported. The signature placeholder undergoes the permitted one-step matching and fixed side-condition closure. A successful attempt assigns the original candidate constant, then inlines temporary support and checks the closed certificate in the original query environment, including its std3 axiom closure. No intermediate proof-body rewriting is required for a failed application. Native import conflicts and unsupported successful-certificate export remain explicit residuals. Candidate vocabulary remains confined to rollback branches. At most one candidate module environment is retained; module replacement and branch close release its regions after the failed branch's Core/Meta references have been restored. Every search branch starts with empty Core/Meta caches. Matching answers are recomputed; query-answer memoization is disabled. Immutable module data may be reused. Content-addressed answer memoization requires prior byte-identical complete semantic JSON for squareVia and twoLayerVia under cold/warm caches and forward/reverse test-unit order. Cold/warm and forward/reverse acceptance compares the verdict, intervals and per-edge JSON bytes.

Per-reading checkpoints use typed Batteries pickle objects and atomic rename. Each attempt is bound to the implementation revision and diff, exact request bytes, source-library path and explicit input fingerprint, index headers, exact closed query telescope, candidate identity and attempt ordinal. Replaying a checkpoint restores its original candidate resource charges and trace; successful closed terms are checked again in the original query environment. All checkpoint regions remain live until process exit because expression sharing can retain mapped query storage after reconstruction. These records are continuations of that reading, not answers shared between queries. JSON remains output only. The make runner starts a fresh compiler after 64 newly evaluated external candidates; the parent waits for exit before starting its successor. This bounds process-global candidate storage across compiler lifetimes. The default checkpoint directory is keyed by implementation revision and request content under `build/lean-inspector/search-reduction-checkpoints`; `SEARCH_REDUCTION_RESUME` selects an explicit directory, and an explicitly empty value disables checkpoints for the uninterrupted comparison. A stopped reading can resume with the same make invocation, directory and exact inputs. Completed attempts are read rather than searched again.

The whole process tree remains subject to the 12 GiB physical-footprint limit. NoHit requires complete membership, primary and fallback enumeration with normal candidate failures. Membership completeness belongs to the query: every missing entry must be checked as ineligible, outside that query's acyclic scope, excluded by a compiled and mutation-tested necessary-condition theorem, or definitionally unequal. Until that theorem and its mutations are verified, unresolved membership entries conservatively block NoHit; a global incomplete bit cannot certify a negative query. Missing data, candidate budget exhaustion, G truncation, load failure and unsupported transport remain unknown and retain their candidate residuals. Whole-tree 12 GiB or wall-clock guards yield interrupted execution; they are infrastructure limits outside R. Complete recall for general N-equivalence and the implementation bridge for query-local constant-closure exclusion remain open.

两条路线独立运行与恢复状态。任一路成功并取得闭合 kernel 证书即为零价；只有两路均正常耗尽才为一价。任一路超时、中断或故障只使该路为 unknown，不会抹去另一路的成功或使整目标执行失败。查表关闭时只重放旧局部路线及其原预算。

只在冻结枚举完整结束时报告 NoHit。缺索引、漏页、未遍历页、部分基底、预算耗尽和中断均为 unknown/insufficient，不计一价。NoHit 只表示冻结 R 未识别，不表示不可证明或本征困难；一步有界推论类不等于全部 B⊢T。`SEARCH_REDUCTION_LOOKUP=0` 只用于重放旧局部路线的消融读数，不冒充新 R 的完整查表。

## 4. 前沿、根探针与 min-max DP

保留声明级 `k=1` 作者边。`k=2` 对每个声明至多追加一个统一的两层祖先前沿候选，不枚举前提子集，不由跳边生成新窗口。新增候选数至多是批内活声明数；声明拆分不得改变窗口规则或生成额外选择自由。前沿仍按 §3.2–3.4 作陈述级解析检验和定价。

根探针总共两次，分别只持 `B_used` 和 `B_used∪S`。成功且经 kernel 复核时，将零价根超边加入两臂共享的候选图；边的前提是证书实际使用的事实，不能用无前提零边抹去 `S` 的成本。基底根探针成功直接提供 bind-only 证书。根探针和两层前沿探针仅在该臂闭合并经 kernel 复核时加入零价边；失败或耗尽不加边，不记一价。作者边的未知仍是 unknown。已有 `R_v1` 成功证书也可支持 bind-only，`R_v1` 不必跑，其旧耗尽不成为新下界。

对种子 `v∈X`，`d_X(v)=0`。其余节点按入边候选取最小值：

```text
d_X(v) = min_e (c_X(e) + max_{u∈prem_X(e)} d_X(u))
```

空前提的最大值为零，无路为无穷。零价证书边只带实际使用的前提；正常耗尽的作者边带全部活的非种子前提。采用 min-max 深度，不对共享前提求和。生产图、DP、区间、回溯与 `classifyGraph` 属于非测试 Lean 核心，模型与生产复用。

未知边以 `[0,1]` 端点计算两臂 `[L_X(T),U_X(T)]`。含无穷时不相减；有未知或必需阶段 incomplete 时不得声称非 bind-only。保留最优路线回溯、证书实际前提及播种 `S` 的使用位置。

另计算 `d_given` 消融：向局部探针提供全部直接前提类型；生产距离 `d_cut` 仍遵守合成前提隐藏规则。在共同图、假设单调的理想重建模型中 `d_cut≥d_given`。若所有读数全等，报告“切式计价无可观测效应”，不把消融值带回生产判词。

## 5. 单源呈现与宽 `S` 排除

基底呈现认证只允许一条实际基底声明 `b`：完整陈述、∧ 投影或 ↔ 两向的有限视图，经带证书的正规化 `N` 后恢复整个 `T`。转换时把 `b` 当抽象假设，其他基底事实不得补实质分量；`b` 的证明只在最终恢复 `T` 时使用。多源组合交给局部重建与图，不充作单源呈现。

查询条件是非中性分量的有向包含 `A(T)⊆A(b)`，不要求键相等。冻结语法的索引必须完整，哈希只定位；跳过候选须有覆盖依据。中性分量是在共同 telescope 下不依赖源或基底、可由 `True`、`rfl` 或无前提 `omega` 闭合的分量，不进键。仿射项使用共同不透明原子字典正规化，算术证书只以单个源分量为前提；定义展开限于经检查的无环非递归别名。一般递归、matcher 和 recursor 保持不透明，归约预算耗尽不得伪装为未命中。索引、查询和证书构造均计预算。

宽 `S` 排除保留基底补分量、打包任一侧、算术、投影、双向恢复、依赖闭包藏目标及集合级拆分/打包的有限呈现检查，并包含单源呈现认证的命中。`S` 及其依赖闭包的分量联合能在 `N` 下直接恢复 `T` 时，不得以该集合制造收益；这不是任意 `S⊢T` 的全局搜索。

`S` 成员若至少有一个非中性分量，且实际匹配一条基底声明的单源呈现，则视同基底。全中性 `S` 不因空集包含而被拒，交给声明图判定；它仍须通过目标泄漏与活路径检查。

### 5.1 target-part 反向探针

除宽排除外，若 `s` 与 `T` 在单射改名后互为陈述子项，或 `R_lookup` 持 `{T}∪B_used` 能闭合 `type(s)` 而只持 `B_used` 正常耗尽，则 `s` 是 target-part，不可作为新增结构种子。每个 `S` 成员至多一次反向探针和一次基底独立探针，成功须 kernel 复核；预算或故障具名 incomplete。该规则防止把真正依赖目标的等价泛化、拆分或重打包当作辅助线。基底已能独立闭合的 `s` 不因反向探针成功而排除，仍须经过单射改名与宽排除。

`T`、其别名/重述以及依赖它的声明不得偷偷进入配对环境。宽排除不因私有名、拆文件或声明包装失效。若 `S` 全为 target-part，不能判非 bind-only。例行可证的合成前提仍可因其陈述提供了隐去的信息而产生约化；防刷边界是 `T` 自身被基底根探针例行闭合时判 bind-only，读数必须保留其 R 和图作用域。

## 6. 判词、closure 与见证边

`classifyGraph` 的三态互斥且穷尽，按以下顺序计算：

门槛 A 为现行定案：满足下面守卫的严格下降即判非 bind-only，强制报告 `closure=zero|partial`；不要求配对距离降到零。守卫采用声明图最优活路径上的实际种子使用，`cut` 与 `proof_hard` 都计入约化，分别报告。

- **bind-only**：取得合规单源呈现证书、`U_B(T)=0`、基底根探针成功或已有 `R_v1` 成功证书之一。
- **non-bind-only[G,R_lookup,k,B_used,closure]**：图提取完整；隔离、呈现与宽 `S` 排除完成；无必需 unknown/incomplete；根处查表正常耗尽；两臂区间有限；`L_B(T)>U_{B∪S}(T)`；存在合规 `S` 种子在配对臂最优活路线实际使用；见证分为 `cut`（已播种的合成 `S` 成员使边从一变零）和 `proof_hard`（最优路径使用的 `S` 顶点满足 `d_B(s) ≥ 1` 且附有 s 对 B 独立查表正常耗尽记录）。`d_B(s)=0` 或独立查表命中的 s 不能作 proof_hard。`U_{B∪S}(T)=0` 时 `closure=zero`，否则为 `partial`。
- **insufficient-evidence**：其余情形。`d_B>0` 且两臂距离相等时另报“未见约化”，不判 bind-only；`S=∅` 时另报“无辅助声明”，不能判非 bind-only。

非 bind-only 读数逐条输出 cut 见证边及其合成前提，或 proof_hard 种子及其基底深度，并输出实际种子依赖、两臂区间和 closure。`zero` 提供沿已核验证书零价闭合的更强读数，`partial` 只说明该图上的剩余构造层减少；两者都不自动取得 `CLAUDE.md` §3.2 的 content 资格。单体证明若基底不能零价闭合而没有具名辅助声明，只能给出“无辅助声明 / 证据不足”。

### 6.1 现在时限制

内联 `have` 不拆，声明体内部例行步骤与内部发明折成一个 `opaque` 步骤。两个见证打包进同一声明会折叠构造层，可能使约化消失而转为证据不足；本契约不宣称任意 helper 拆并保持距离，也不要求为了读数制造辅助声明。

图外短路线可能消除图上的正差；猜测型绕路也可能抬高作者路线距离。窗口不能覆盖所有替代证明。声明粒度与证明项粒度的距离无统一大小关系，不能宣称互为上下界。

在假设单调的模型中，增加种子不增每臂距离；增强 R 也不增每臂距离，bind-only 对 R 增强向上单调。实际固定预算过程须另核验该前提，不能把超预算当正常失败来推单调性。

距离差 `Δ` 对 R 增强不单调。例如 `B={b}`、`S={s}`，`b→s`、`b→t`、`s→t` 初始代价均为一时 `Δ=0`；只把 `s→t` 降为零可使 `Δ=1`，再把 `b→t` 降为零又使 `Δ=0`。重建者强度的单调方向由 bind-only 的单调性承担，不能替换成 `Δ` 单调。

## 7. AURIC FIB 与 ATOM 假设

AURIC 不提供 P 侧边价，也不改变 P 侧判词。实际 `LawFact.separated` 给出 `strict`，`LawFact.identifiable` 给出 `collapsed`，均未取得则 `unknown`。同族同域 strict 与 collapsed 互斥，三态穷尽；正宽度、正 `Δ` 或单点数值不能代替 LawFact。这里 FIB 的 `Δ=rκ−XY` 与图距离差是不同读数。

有限候选域双前提模型只提供单向桥：数据元变量不共享、计数律为积律且 `z=0` 时，`Pyramid.delta≡0` 并可得 collapsed；同一族内若存在边际相同、联合坐标不同的两个可实现耦合，且所需四格质量为正，则得到 strict。变量共享或四格非空本身不保证存在这样的两个耦合。逆命题不成立：常值律可 collapsed 而 `Δ>0`，strict 的二点族也可在常数规模枚举，不能推出搜索下界。既有观察的后处理和常量身份元数据不切开观察纤维；完整状态身份能否切开须另证。

FIB 五模式单元刻画两个选择的耦合，不刻画是否存在选择。任意两个布尔特征配任意测度，取 `z≡0`、`r=1` 即可表示五模式律；任意超边二元化本身也不提供难度信息。因此“所有证明可拆成 FIB ATOM”的无约束全称形式不作定价或判词依据，`c=1⇔共享数据元变量(strict)` 也不是契约。

计算面中的合法角色限于上述单向模型桥、猜测边上的静态 `coupled/independent` 注记，以及预登记的 `shared_data × c` 交叉表。它们不引入新的 LawFamily/Application 适配器或 FIB 来源定理。作者另可按 §7.1 提交既有合同表达的信息面证据。

静态注记只读取消费者陈述的逻辑骨架：经可约头正规化后，若一个 `Exists` 的非证明见证变量同时出现在其作用域内某个 `And` 的两侧，则 `shared_data=true`、`coupled`；否则为 `false`、`independent`。递归范围是 `forall`、`Exists`、`And` 和 `Or`；外层已给定参数不作为待选见证。`independent` 只表示该骨架未检出共享，不声称任意隐藏谓词、切式或证明实现语义独立，更不构成 strict/collapsed 证书。读取失败为 unknown；该注记不参与定价、种子排除或判词。

交叉表的总体、注记定义和夹具预测须在运行前登记。表按基底臂候选边的 `shared_data∈{false,true}` 与 `c∈{0,1}` 计数，明确包含作者边、两层前沿和根探针边；unknown 价和缺少注记分别报告，不填入任一布尔单元。`d_cut/d_given`、无辅助声明数与 opaque 声明数随同报告。

更强的 ATOM 完备性命题保持研究开放问题：必须事先固定证明语言、FIB 网络、可执行编码 `E` 和解码语义，证明覆盖、语义保持与反射、作用域保持、证书可译回和资源对应；映射不得按结果事后选择。受限网络须先检验能否表达三元 OR；只有二元化或同名对应不能完成这些义务。

### 7.1 可选信息面

信息面报告原问题 `T` 在已登记粗观测下的不可约性，与计算面并列（parallel-only）。它不说明 `S` 切开了纤维，不补足距离下降，也不单独支持非 bind-only；collapsed、unknown 或不提交均不构成 bind-only 证据。删除信息证据后，计算面判词和计算字段的 JSON 投影逐字节相同。

唯一输入是以确切 `T` occurrence 索引的既有 `Contract.AuricFib.Application` 的 `Evidence.law`。取得 `strict-bound` 须同时满足：

1. client 索引是该原目标的完整、未应用 occurrence，类型与刚性宇宙一致。
2. `client.source` 经安全数据别名展开后的头是 `Analysis.Source.ofRegistration`；其 `DependentFamily.Registration` 正是同一报告中 `T` 经普通四槽审计取得 DTR-Declared（`declared_validated`）的登记，不接受手写 Source。报告携带本次普通审计记录。
3. `family.role` 属于该登记 selection 的读出；来源 selection 必须与普通登记一致，复用完整重建和实际读出对应检查。
4. 有实际 `LawFact.separated`，且事实的 `uses_target_results=false`。正宽度、正关联坐标、数值点均不能替代它；目标依赖检查复用既有编译证明体检查。
5. `family.law`、`family.domain` 及所选实际读出表达式用到的编译常量与 `S` 不交，包括能到达 `S` 的传递依赖。
6. domain 不是自由单纯形。自由单纯形覆盖证书不合格；没有该证书也不足以证明非自由。现行机械路线只接受 Boolean 参数族（至多两条律，不能覆盖五模式自由单纯形），其他形态具名 fail-closed。

任何绑定条件不满足、形态不识别或检查不完整，均报 `not-bound(<具名原因>)`。共同绑定检查成立时，沿用 `LawFact` 与 `classifyCapture`：separated 为 `strict-bound`；仅 identifiable 为 `collapsed-bound`；两者均无为 `unknown-bound`。后两者只是缺少第 4 项正证据的并列读数。没有提交则为 `not-submitted`。不改 Interface 合同，不以 Python 或 JSON 作语义判定。

每条搜索报告输出 `information_face`、`information_application`、`information_registration` 与 `information_ordinary_records`。`information_tag` 只在 `strict-bound` 时取值：计算面非 bind-only 为 `both`，证据不足或未下降为 `information-only`，bind-only 为 `conflict:strict-vs-bind-only`。conflict 是 strict 不推出难度的校准读数，计算判词仍为 bind-only；其余标签为 null，不合成分数。请求以可选的 `information <Application名称>` 提交证据。

信息面模型复用 strict/collapsed 互斥、capture 穷尽和 `postprocessing_no_new_separation`；另核验计算投影与可选证据无关、存在零计算距离而 separated 的原目标，以及 separated 对域扩大单调。`S` 绑定版（证明 `S` 切开 `T` 的基底纤维）保持 open 后继，需要实际输入及其对应证明；它不作为本接口的隐藏承诺。

## 8. 模型核验义务

模型定理的公理闭包须包含于标准三公理 `propext`、`Classical.choice`、`Quot.sound`。必须陈述一般图、探针与证书之间的关系，不以结论作假设，不用常数事实替代模型性质；已有 DP、Bellman 等价和单调结果直接复用。以下义务逐项核验，未完成者明确列 open：

1. DP 等于最小 min-max 深度，并支持最优路线回溯。
2. R 对假设单调时，扩大种子不增距离。若 `d_X(v)=0`，且 `v` 对所有候选消费者（含根探针与两层前沿）都是解析前提，加入 `v` 不改变可见假设和定价，因而不改变任意 `w` 的距离；若 `v∈X`，加入它也不改变距离。无条件的零种子冗余不成立：存在零价可得的合成前提，在播种后使另一条边从一变零并使目标距离严格下降。
3. 解析拆分、零价细分与活路径外前提不改变距离；零价路径证书可装配并由 kernel 复核。
4. 在相同图及相应单调前提下 `d_cut≥d_given`。
5. `S` 全为 target-part 时不判非 bind-only；非 bind-only 必有 cut 或 proof_hard 见证。
6. R 取顶时所有非种子步骤零价，取底时所有非种子作者步骤一价；存在分别取得两类判词的模型图，实际提取图的非退化另由校准检验。
7. 三态互斥且穷尽，unknown/incomplete 不判 content；bind-only 对 R 增强单调，并给出 `Δ` 不单调反例。
8. 存在 `d_decl<d_term` 的图，也存在 `d_decl>d_term` 的图，禁止从粒度变化推出单向界。
9. 任意两个布尔特征的律都可表示为 `z≡0` 的五模式律；AURIC 单向桥及逆命题反例保留。

## 9. 可证伪校准与读数

验收在真实编译声明提取图上进行，不手填边权。冻结 R 配置后先跑现有校准夹具与真实负例，再跑受益单元；预测不成立时照实报告，不调整允许表、顺序或预算。

- 校准与登记单元应同时出现 bind-only 和 non-bind-only；否则报告校准失败，不能用手造模型图替代实际提取的非退化检验。
- `doubledContent ← addition` 的预测为 `d_B∈{1,2}`、正约化、`closure=zero`，`Lean.Omega.*` 只作叶或不出现；替换 `addition` 内部闭合器不改变该声明图读数。若根探针直接闭合 `T`，如实判 bind-only。
- `squareVia := ⟨42,squareFact⟩` 的预测为一到零、zero，`squareFact` 是合成前提且自身不被误记为难；真实依赖它的两层链预测为二到一、partial。`S` 必须出现在作者证明的活依赖中，只有作用域可见不算。
- unwrapped、splitHelper、specialized、package、dead、等价泛化及目标本身例行的 `routineVia` 夹具均不得判非 bind-only；单独知道某个合成辅助陈述例行可证不构成排除理由。单源呈现、宽 `S` 排除、全中性 `S`、私有名与词汇传输回归保留；判词变化逐项说明适用规则。
- 登记声明逐条报告是否越过词汇阶段、顶点和边数、合成前提数、两臂区间、判词、closure、unknown 原因、见证边、耗时与整棵进程树的物理 footprint 峰值。
- 同时报告 `d_cut/d_given`、`shared_data × c` 交叉表、“无辅助声明”数量与 opaque 声明数量。切式消融全等时如实报告无可观测效应。

## 10. 资源边界

顶点数不超过活闭包内批内声明数加 `|B_used|`。每臂每顶点至多两次声明探针，另有两次根探针、每个 `S` 成员至多一次反向探针和一次基底独立探针，每次 `200000` 心跳。没有证明项顶点容量扩容或子项义务搜索路径。

内存为一份共享不可变基底导入，加 `O(Σ|type(v)|+|前提|)` 的当前目标数据；证明体仅线性遍历取依赖，目标结束即释放，不跨目标常驻增长，不建立全库索引。探针串行执行，整棵进程树物理 footprint 不超过 `12 GiB`；超预算记 unknown。导入环境的基础驻留另行实测，不能冒称与库大小无关。

## 11. 与现行准入的关系

本契约只提供搜索约化的 Observe 读数，不替换 `CLAUDE.md` §3.2 的判形、活路径、有消费辅助声明、模块准入依据或开放问题结算规则，不替代 §3.3 用途规则、§3.9 四槽义务和 AURIC 来源绑定。把带作用域的 non-bind-only 升级为 §3.2 content 或修改该条，必须另获 owner 裁决；模型定理、实现通过与校准读数都不能代替。

“只要能写出 Lean 代码就是非 bind-only”会把别名和薄包装当成新内容；无界地把已证明结论全部免费提供又会使 content 为空。本契约固定有限图和可复现重建者，把“变容易”落实为声明辅助构造层数之差，并保留证据不足、作用域和未决边界。
