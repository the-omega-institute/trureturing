# 搜索约化逃逸审计契约

## 1. 目的与边界

本契约观察一个已交付、经 Lean kernel 接受的证明，判官读取作者声明图与探针零价边构成的有限声明子视图，判断加入具名辅助结构 `S` 后，到达原目标 `T` 所需的辅助构造层数是否减少。约化量为 `Δ = d_B(T) − d_{B∪S}(T)`。构造包括选出中间陈述或见证；给定一个陈述后能例行证明它，不等于选出这个陈述是免费的。

结果永远是 `Observe`，不产生 Block、总分、权重或新的准入状态。依赖提取、局部重建、距离和判词由 Lean 计算，成功证书由 kernel 复核；JSON 只是投影，不读回作语义判断。旧结算保持原有基底、配置和结论。

“更容易”只指登记的声明图、局部重建者和预算内的读数，不是绝对证明难度、原搜索问题的复杂度或 P/NP 证书。作者路线可能遗漏更短证明；两臂各自的上界不能相减成为全局搜索收益的下界。局部过程按序执行也不推出多项式时间。

极限静态图是以全部可写命题和一步推理超边描述潜在推导的解释性模型，程序不实现它，判词不陈述其上的最优、必经或下界。理论卷 A-20.3 只作说明性引用，不在本契约复制，也不由程序读取。

## 2. 登记、基底和共同环境

校准前固定原任务 `T`、交付批次、候选 `S`、声明图提取配置、`R_lookup` 的允许表与顺序、预算、工具链、词汇传输配置及窗口 `k=2`。判词相对 `(G, B_T, R 版本, 证书池)`；每条读数带 `[G, R_lookup, k, B_used]` 及配置身份。不得为受益声明调整允许表、顺序或预算。

`T` 和声明类型保留完整 telescope、局部假设、宇宙、量词与依赖关系。`B0` 是受保护提交、钉版依赖及冻结 D5 的规范清单，只排除目标交付及其污染闭包；仅被交付导入的既有前置不排除。Lean 生成清单，并核验实际载入清单 `B_load ⊆ B0`。读数报告载入清单、`|B_load|/|B0|` 和模块 scope；作者 imports 不定义规范基底。

`B_used` 是图上已核验可调用的种子，其已取得身份须带证书；受保护常量须通过隔离核验，满足 `B_used ⊆ B_load`。图上负读数相对登记的 `B_T` 和实际可见前提，不上传为全 `B0` 的搜索结论。合规的 bind-only 证明或单源呈现证书可以从子基底用于较大基底；有限耗尽加配对证书不能这样上传，也不证明增强后的重建者仍会找到或仍会失败。

两臂共用一份核验后的词汇和不可变基底导入。探针不获得作者证明体、作者属性、simp 表、批内实例注册、初始化器或全库索引。私有常量按 Lean `Name` AST 传输，包括数字段，不经文本名重建。缺片、隔离失败、不支持的形态与故障均具名记为 `incomplete`，不等同正常穷尽。守卫预算耗尽仍 incomplete；R 查询的 κ/G 停点按 §3.4 分型定价。

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

基底臂种子 `X=B_used`，配对臂种子 `X=B_used∪S`。两臂使用同一候选框架、同一个定价函数和同一预算；种子改变可见前提、实际支持与证书边，引起局部重定价。所有局部探针只读声明陈述，不读其证明体。

对非种子消费者 `v`，`R_lookup` 只获得其种子前提与解析前提的类型作为假设：

- `c_X(v)=0`：探针闭合 `type(v)`，证明通过 kernel 复核。零价边保留证书**实际使用**的前提；其深度是所用解析前提深度的最大值，种子前提深度为零。
- `c_X(v)=1`：冻结允许表的全部尝试正常结束仍未闭合。作者边保留全部活的非种子前提，其深度为这些前提的最大深度加一。
- `unknown`：Fault、NotRun、缺件或未登记停点的不完整读取；无价格。登记的 κ/G Miss_R 仅给已有作者边一价，守卫仍未完成。

边的单位是辅助构造层，不是作者证明体中的原语数、数据实参个数或历史搜索回溯次数。一个局部 `rfl` 可证的具体等式仍能作为存在性目标的合成辅助线；选择该等式所携带的见证可有代价。

隔离重建为每个 `(T, S 成员或其传递命题依赖)` 完整重述检查分配独立的 `200000` 对外心跳。检查域按声明名固定顺序去重；单源呈现与全部 legacy 分支（可约头与域匹配、显式子项归约、逻辑引入与投影、基底组件与 omega、递归 And/Iff）共用单元额度，递归子项不重置。其余重建保留原累计 `200000`。预登记上界为 `(m+1)×200000`，其中 m 为检查对数；逐单元报告耗用，内部心跳为对外单位的 1000 倍。单元超限保留守卫名、检查对与停点，处置为约化未获认证、不准入。

### 3.4 `R_lookup`：冻结闭合表与一步查表

闭合表按以下顺序冻结，旧局部闭合路线保留独立的 `200000` 搜索心跳预算。查表对每个候选独立分配 κ = `200000` 搜索心跳及 `8000000` 准备心跳。候选的全部视图、实例化、副条件闭合、证书组装与最终 kernel 核验共用 κ；每次候选尝试均从分支初态开始并重置 Core/Meta 缓存。视图遍历不设独立深度上限，全部工作计入 κ。搜索 κ 超限记结构化 searchKappa，枚举继续；准备或执行异常保留具名 Fault。每个停点报告模块、名字、原因及两份预算消耗，超过 κ 不属于正常穷尽。

搜索计入查询规范化、视图生成、实例化、合一、实例合成、闭合表义务、新证书构造与最终 kernel 核验。准备计入索引读取、olean 加载、签名与证明体的确定性词汇搬运和重建；这些物化操作不选择候选、不创建或赋值查询元变量。已认证 B0 的内联证明载荷不重复做中间 kernel 复核；重建计算声明的合法性及最终查询环境中的闭合证书仍经 kernel 检查。心跳均以 Lean 对外单位报告，内部读数为其 1000 倍。

每查询另有覆盖上界 G = `340000000` 对外心跳，计量候选搜索与准备之和。每次 R 查询使用互斥终态 `Hit(cert) | Miss_R(exhaustive | searchKappa | coveragePrefixG) | Fault(reason) | NotRun`。Hit 只由合规 name-only 证书经 kernel 重放取得，价格为 `some 0`；实际冻结调度到达登记停点且无证书的 Miss_R 价格为 `some 1`；Fault 与 NotRun 无价格，保留未知区间。停点来自结构化执行字段，不从诊断字符串推断。单个候选 κ 耗尽只结束该候选，调度继续；未被正证书吸收的 Fault 优先于随后 κ/G 停点。准备失败、缺数据、中断与 OOM 不定价。允许表、候选顺序、κ、准备上限和 G 不按读数调整。

Miss_R 只给已有作者边定价，不制造 shortcut、根边或零 closure。所有零价新增路线均来自正证书；零 closure 还须实际装配并核验零路线。守卫独立消费 `guardRun`：只有 Hit 或 exhaustive Miss 提供其所需的完成信息；预算 Miss 不解除 target-part、单源呈现、宽 S/换装、来源或隔离守卫。And/Iff 子查询保留全部结构化停点和 Fault，不能用后继停点掩盖先前故障。

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

对每个叶目标至多应用一条 B_T 声明，允许全称实例化、And/Subtype 投影、带证书的 Iff 方向与等式方向。数据参数只由目标、可见 Γ 的合一或冻结实例机制确定；剩余命题义务只交上述闭合表。不猜见证，不发明切式，不递归查表。成功证明项须经 kernel 复核且公理闭包包含于标准三公理。零价边只携带证书实际使用的可见前提；没有局部依赖的命中是零叶。

查表是二值关系，不使用频度、惊奇度或重复登记次数。完整陈述的成员查询以规范化 N 后、α 等价不变的完整陈述哈希为键；推论查询以规范化结论的判别树键路径为键，并包含 And 投影、Iff 方向与必要通配视图。键只负责召回，实例化、`isDefEq` 与 kernel 证书决定命中。变量改名、全称参数次序、投影、Iff 方向和实例的等价写法均须经过召回验收；未证明覆盖的键筛选不能支持 NoHit。

磁盘索引契约要求独立生产者按模块分片、分页写出，并对账受保护 B0 清单。索引按基底数据输入与显式版本号复用，不哈希程序字节。消费者将完整路由 manifest 物化为堆数组，命中页及必要通配页通过 mmap 读取，只复制命中元数据；当前实现尚无总额外索引内存为 O(命中) 的严格上界。消费者不对全环境建树，不调用 `exact?`、`apply?` 或 `LazyDiscrTree` 全库树。总内存还包含 Lean 导入闭包与缓存区域。

The current backend is `R_lookup/v19/obvious-v1/lazy-interval/scope-B_T/primary-index-only/candidate-200000/preparation-8000000/G-340000000/memo-target-basis-R-v3/N-memo-2000000/checkpoint-v6/views-kappa/isolation-independent-units`. `make search-reduction-index INDEX_BASIS=<protected-commit> INDEX_DIR=<build-directory>` produces the index offline. Reuse depends on compiled basis data, the Mathlib pin, Lean version and explicit format versions. Implication candidates use Lean core `DiscrTree.mkPath` and `getMatch`, including projection and direction views. Batteries pickle/withUnpickle supplies module shards and mapped compacted storage. Candidate order is a stable partition with already loaded owners first, followed within each partition by module name and module-local declaration ordinal. R v19 excludes dropped `[*]` and `[Eq,*,*,*]` star-fallback keys from production enumeration; the static-pruning implementation is outside the production candidate space. Implication candidates are filtered to B_T without changing their module-local order.

`staticStarImpossible` and `LookupModel.static_star_impossible_no_certificate` describe an independent static-pruning interface. This interface does not participate in the production candidate space or current NoHit accounting.

`SEARCH_REDUCTION_PROFILE=<path>` records production phase boundaries, including imports, isolation, presentation, structure exclusion, graph extraction, pricing, certificate assembly, independent negative replay and publication. Nested replay spans are reported separately. The production command always checks the transitive original dependencies of the production run's existing baseline and paired zero certificates and emits `PRODUCTION_SOURCE_AUDIT`. Baseline certificates exclude T and registered S; paired certificates exclude T. These checks reuse the assembled certificates and do not repeat graph evaluation. Neither option changes R's candidate scope, order, budgets or classification.

The preparation allocation is the fixed R v19 budget of 8000000 heartbeats per candidate. Preparation exhaustion is a Fault and is unpriced; the allocation is unchanged throughout calibration and replay.

Exact membership has the independent format `R_lookup/membership-alpha-syntax-v5-qualified-parts-memo-2000000`. Both producer and query normalize the complete statement, preserving its telescope, using the shared frozen syntax normalization from the presentation path, with beta/zeta preprocessing. Only noncomputational acyclic aliases unfold; recursive computations, matchers, recursors and instance dictionaries remain opaque. Metadata, binder names and binder annotations are removed; universe parameters receive canonical names in occurrence order. Alias-stack-sensitive memoization preserves N's result. Production and queries use the same fixed 2000000-node normalization fuel. The de Bruijn expression's core hash addresses one disk bucket containing a hash map. Only equal-hash entries undergo the existing definitional-equality and certificate checks; collisions never certify a proof. `make search-reduction-membership-index-run INDEX_DIR=<directory>` adds this sidecar to an existing complete implication index. The sidecar binds to that index's compiled-input fingerprint. Each module retains the first eligible copy of a name across main, server and private parts; ineligible placeholders do not consume membership identity. The ordinal remains the name's first occurrence across all parts, and identities remain (module, Name). A selected declaration that is unavailable or ineligible in the imported environment is recorded as missing and prevents completeness. Missing membership data, normalization failures and unreadable buckets cannot certify NoHit.

The implication scope is B_T = B0 intersected with the target owner's transitive import closure, extended by registered prerequisites, after excluding the delivery batch, T and its reverse import pollution closure. Eligible target ancestors are imported once when constructing the isolated target environment. The implication search performs no imports or vocabulary transport; it only applies candidates whose original module and Name are already present in that baseline and whose owner belongs to the explicit target/prerequisite closure. Extra Mathlib modules loaded for fixed tactic execution do not enlarge B_T. One-step consequences of library theorems outside this closure are not counted. Every verdict reports scope=B_T. Model candidate lists and scope-dependent obligations quantify over B_T; they make no full-B0 implication claim.

Production requests and graph calibration derive this scope with the same `targetBaselineImports` function from the target owner's compiled imports and registered prerequisites, and initialize lookup budgets and memo state with `onDemandLookup`. A complete fixture index does not enlarge it. In particular, `GraphCandidates.squareVia` imports Lean and Omega; `Nat.exists_mul_self` belongs to Mathlib outside its B_T and cannot supply a zero-price implication. With the registered `squareFact` seed the calibration asserts [1,1] to [0,0], non-bind-only with closure=zero. This is a limitation of B_T even though the broader fixture environment contains that Mathlib theorem.

Exact alpha-equivalent membership still queries all eligible B0 by the independent statement hash. Eligible members are all safe compiled theorem, definition and opaque declarations owned by eligible B0 modules, including private, deprecated and metaprogramming declarations. Constructors, inductives, recursors, axioms and unsafe declarations are outside this member class. The implication suggestion blacklist is not a membership filter. Every eligible declaration must be indexed or recorded as missing; any normalization or loading failure blocks complete NoHit. A hit has zero price. Only an external membership candidate's own module is imported for certificate construction; candidate matching, source isolation, the closed kernel check and std3 axiom closure remain mandatory. No external implication path participates in pricing. Temporary certificate support is inlined into the original query environment, preserving the registered local assumptions and excluding T and S.

Compiler-generated safe auxiliaries remain eligible for exact membership, alongside author-written private theorems; their folding into author vertices does not remove their existing B0 facts. Certificate reconstruction and kernel checking can share expression storage with imported module mappings. Mappings backing an exported certificate remain live until the compiler exits; unsuccessful candidate mappings are released after restoring branch state. Membership eligibility is independent of this storage rule.

Every search branch resets Core/Meta caches. Immutable module data may be reused. Primary recall keeps at most 64 exact closed query telescopes in the table-local memo, with environment identity checked before reuse. Within one target evaluation, identical closed (goal, ordered premises) queries are priced once. Across runs, typed Batteries pickle answers are keyed by the target identity and exact statement vocabulary, protected B0 compiled-input and membership versions and delivery exclusions, the B_T environment, explicit source-input fingerprint and R version. The full key is checked after hash lookup; collisions cannot supply answers. Successful cached proof terms are kernel-checked again against the exact query telescope and actual premise selection. JSON remains output only. `SEARCH_REDUCTION_QUERY_CACHE` selects a cache directory; an empty directory setting disables disk persistence. `SEARCH_REDUCTION_MEMO=0` disables both answer caches. Acceptance requires byte-identical complete semantic JSON for squareVia and twoLayerVia under cold/warm caches and forward/reverse unit order; either failing cache is disabled.

Per-reading checkpoints use typed Batteries pickle objects and atomic rename. Each attempt is bound to the explicit R version, exact request bytes, source-library path and explicit input fingerprint, index headers, exact closed query telescope, candidate identity and attempt ordinal. Replaying a checkpoint restores its original candidate resource charges and trace; successful closed terms are checked again in the original query environment. Replay beta-reduces the closed certificate applied to the current context before support extraction, so unused context arguments do not become graph premises. All checkpoint regions remain live until process exit because expression sharing can retain mapped query storage after reconstruction. These records are continuations of that reading, not answers shared between queries. JSON remains output only. For membership certificate continuations the make runner starts a fresh compiler after 64 newly evaluated external candidates; the parent waits for exit before starting its successor. This bounds process-global candidate storage across compiler lifetimes. The default checkpoint directory is keyed by explicit R/checkpoint version and request content under `build/lean-inspector/search-reduction-checkpoints`; `SEARCH_REDUCTION_RESUME` selects an explicit directory, and an explicitly empty value disables checkpoints for the uninterrupted comparison. A stopped reading can resume with the same make invocation, directory and exact inputs. Matching completed attempts are read rather than searched again. An ordinal occupied by different input data is a cache miss and is recomputed; no stored verdict or resource charge is used for the mismatched attempt. Program bytes, Git HEAD and working-tree diffs are excluded from reuse identity; incompatible implementations require a manual explicit-version bump.

### 3.4.1 Whole-probe cache trust contract

`make search-reduction-run` uses `SEARCH_REDUCTION_PROBE_CACHE` for authenticated whole-probe records; `0` disables this cache. Python performs input identity, byte authentication, entry selection and process scheduling only. It neither reads verdict JSON nor classifies a graph. Reuse identity contains request bytes, Lean/toolchain and dependency pins, the D5 and frozen-state populations, the selected index and source-library populations, semantic environment options and explicit cache/R versions. Program source and compiled judge bytes, Git HEAD and working-tree diffs are excluded. Lean records the mathematical module files selected from the target/additions' dependency closure and the target/prerequisite import population, including main, server and private parts and absent optional parts; the runner checks their authenticated content fingerprints before reuse. Runtime/compiler packages and judge implementations are pinned by explicit versions rather than program-byte hashes.

A reusable record comes only from a successful complete cold request. Before cold R computation, Lean selects mathematical input files and the runner snapshots their fingerprints. After exit 0, the runner rechecks the outer input identity and mathematical file snapshot, authenticates every record file, and atomically publishes the signed manifest and record directory. A changed input or failed snapshot check prevents storage; it does not withdraw a cold observation already output by that run. A failed cold process cannot create an accepted record. A complete single-probe plan can use its authenticated Lean replay entry and typed request payload. Partial or multiple-probe plans retain the original request wrapper so that entry selection cannot omit a requested probe.

On an authenticated hit, the runner checks the current input population and stamps, record identity, HMAC, every record file's content hash and mathematical source-data fingerprints. Lean deserializes the typed record and checks its request identity. The hot path reuses source imports and successful request elaboration, presentation search, structure reconstruction, graph extraction, pricing, interval computation and independent negative-guard search replay. It retains the recorded NoHit and unknown outcomes and their explicit R semantics. It does not rerun negative enumeration or prove object-level unprovability. Any change to R's candidate space, ordering, budgets, completeness accounting, negative semantics or other incompatible procedure behavior requires an explicit version increment, including synchronized Python `R_VERSION` and Lean configuration changes. Current kernel certificate checks and classification cannot repair a stale negative enumeration accepted under an unchanged version.

The hot path kernel-checks every cached certificate in the current process and checks their complete axiom union against `{propext, Quot.sound, Classical.choice}`. It repeats the source-dependency audit: baseline certificates exclude T and registered S, and paired certificates exclude T. It publishes a fresh `GraphReading`, defines the current verdict by `classifyGraph` applied to that reading, and kernel-checks the classification equality and its explicit NoHit-premise interface. It exports the current audit module and observation. Certificate, source audit or publication failure cannot become a successful cached verdict; a failed hot process falls back to the original cold request, while exit 75 remains a continuation request.

Cold cache construction either stores typed dependency declarations for live kernel replay or kernel-checks them before exporting an ordinary dependency `.olean` module. Hot module imports use Lean's ordinary compiled-module trust boundary: their declaration bodies are not all replayed through the kernel on every import. The runner authenticates those module bytes together with the typed record and replay entry. Current certificate terms still cross the kernel, their axiom closure is checked, and classification still runs from this invocation's published graph. This boundary depends on trusted cold construction, the local Lean/compiler environment and authenticated storage; it is not a theorem of cold/hot environment equivalence.

The HMAC-SHA256 key is a separate per-user 32-byte secret at `~/.cache/trureturing/search-reduction/probe-auth-key`, outside caller-selected record directories, with no group/other access. A new key invalidates old signatures. Record manifests, mathematical snapshots and fingerprint memos are authenticated with that key; an editable checksum or JSON projection is insufficient. The boundary does not protect against an actor who can replace the trusted launcher/compiler or read/use that user's key.

The stat memo maps each absolute file path and complete `(device, inode, size, mtime_ns, ctime_ns)` stamp to its content hash. Every identity check enumerates the complete current population and reads every file stamp. An authenticated tree aggregate avoids repeated member serialization/hash updates only after the full ordered member list, all current stamps and the memoized member content hashes agree; separately published file and tree memos cannot authorize an aggregate for different member hashes. Selected mathematical files use one stamp read each, including detection of missing optional files. These optimizations assume a stable local filesystem on which a changed file changes its complete stamp. They do not detect content edits preserving the complete stamp, filesystem rollback restoring stamps and bytes inconsistently, or concurrent mutation after preflight. The pre/post cold checks detect observed changes and refuse cache publication; they do not provide an atomic filesystem snapshot or eliminate these races.

Required CI's `current` compiled-audit path calls `make compiled-judge-test` and includes the aggregated Lean audit tests. The dedicated `make search-reduction-test` path additionally executes the Python cache-authentication/input-binding regressions, the runtime shared-closure regression, missing-production-index rejection and telemetry checks, as well as its serial Lean module suite. Success of one path does not claim execution of the other's extra runtime checks. Local dedicated checks do not replace the remote required result. The dedicated suite uses fixture indexes; production measurements use the explicitly selected protected production index and source library. Resource readings describe the sampled process tree and actual build/cache state, not a hosted cold-build capacity guarantee.

The whole process tree remains subject to the 12 GiB physical-footprint limit. Missing data, load failures, unsupported transport and interrupted execution are unpriced faults. Exhaustive guard completion requires complete membership and complete primary-index enumeration with normal candidate failures; budget Miss_R never supplies that completion. Membership completeness is query-local and unresolved entries block exhaustive completion. Whole-tree memory and wall-clock limits are infrastructure faults outside R. Complete recall for general N-equivalence and the implementation bridge for query-local constant-closure exclusion remain open.

The local closure route retains its independent original budget. An unabsorbed local execution fault prevents a combined negative price; a kernel-checked hit from either route may absorb it. Typed query records retain candidate κ, coverage G and fault fields even when a later positive certificate wins. A1 applies the v18 price mapping to those same records: budget misses remain unknown. B applies v19: budget misses have price one. Both projections preserve every guard completion state and the checked upper-route bounds. Neither projection reruns search or migrates an old negative record.

Reuse domains include the explicit R v19, execution-stops-v2, checkpoint-v6 and probe-cache-v9 identities. Old unknowns and negative caches are not migrated. Program bytes remain outside reuse identity. Cache replay preserves typed terminals and current kernel certificate checks; a cache hit cannot upgrade Fault, NotRun or an incomplete guard.

### 3.5 Lean 显然证书与惰性否定

证书语言固定为 `obvious/v1/name-only`：`by_close | by_lookup <ident> | by_member <ident>`。语法类别 `obvious_certificate` 没有 term、tactic、显式见证、数据项、方向、投影路径或引理列表槽。两臂共用同一语言、主索引范围和重放器。证书作者、LLM、核心提名器及 R 都是不受信的生产者。

重放器从实际图顶点构造完整 telescope，并按该臂可见的 Γ 创建局部假设。`by_close` 只运行冻结闭合表；`by_lookup n` 要求 n 属于当前目标的主索引召回和 B_T，再运行相同 κ、实例机制、投影和方向的单候选尝试；`by_member n` 要求全 B0 α-哈希召回，再运行 `isDefEq`。范围外、star-only、缺索引、超限或失败的证书均不能记零，也不能记一。成功保留闭合证明项，经过 kernel 与 std3 闭包检查；生产命令逐臂审计其原始传递来源。证书集合不扩大 R 的接受范围。

`#search_reduction_certificates [by_close, by_lookup n, by_member m]` 提交下一份请求的受限数据池；`#search_reduction_nominations "出处标签" [n, m]` 追加仅含名字的提名。LLM 接口只接收名字与冻结的模型、模板、次数出处，不调用 LLM、不保存思考文本。R 的命中须再由单名字证书重放后导出；不能用一份单名字证书重放的组合命中保持 unknown。`SEARCH_REDUCTION_NOMINATORS=core` 启用 Lean 核心 MePo 与 SineQuaNon，各提名至多八项，在目标局部的冻结预算内运行一次；默认只使用已提交的数据、成员哈希和冻结闭合表。核心分数、提名顺序与重复次数不参与代价。已提交的名字先按去重后的规范顺序核验，再核验自动成员哈希提名。`#search_reduction_edge_certificates head [by_lookup n, by_member m]` 将同一语言的证书绑定到指定声明边，两臂共用绑定；名字仍须通过原范围检查。

先核验两臂全部边和根的证书。基底上界为零时可认证 bind-only。`U_B ≤ U_{B∪S}` 时停止完整 R 搜索，并按已完成数值与守卫证据发布 no-gain_R 或 incomplete，不执行任何完整 NoHit 搜索。只有 `U_{B∪S} < U_B` 时才请求基底根、候选见证边及 `L_B` 最优路线上的 unknown 作者边的 R；每个请求的相同查询由原有缓存结算，Fault/NotRun 保留 unknown，实际 κ/G Miss_R 按 v19 定价。只在 `L_B > U_{B∪S}` 且其他守卫完成时授予阳性。配对边和配对根不运行完整否定。决定集还包含 target-part 反向查询：严格区间下降、基底根已取得定价 Miss_R 和图完整性均成立，且所选种子的独立探针完成 NoHit、反向正证书仍未决时，才按成功优先的原有 R 补跑该反向查询；命中即停。反向 NoHit 只解除种子排除的未决状态，不计入任何图边价格。没有两臂全边守卫，也不要求有限的配对下界。

当 `S=∅`、两臂上界相等且非零、默认正证书核验未闭合目标时，两臂保持 unknown，判 insufficient，不追加完整 R 查询。作者证明使用了某条基底引理，不等于已提交并核验该引理的名字证书；零次完整 R 查询既不是 NoHit，也不是 bind-only 证据。

每个目标的生成审计模块执行 Lean 命令，保留逐边类型化的代价记录、`ObviousCertificate` 声明和 kernel 核验的证明声明。JSON 仅投影这些 Lean 计算结果，不作为判词输入。判词绑定图、B_T、R 版本、语言版本与规范证书池摘要；扩充证书池可以推翻旧阳性，不改写旧结算。NoHit 仍是完整机械 R 的相对否定；提名器或 LLM 未命中不能认证一价，也不能推出绝对不显然、不可证明或复杂度分离。

`SEARCH_REDUCTION_FULL_EVAL=1` is a differential-test mode: it evaluates every unresolved baseline author edge and every eligible seed's independent and unresolved reverse query, without requesting paired negative prices. It uses the same candidate domain, budgets and classifier. `SEARCH_REDUCTION_B1_COMPARE=1` additionally measures the unsplit parent enumeration when a split is incomplete, then restores the split's Meta state and semantic budget accounting. Its comparison events are diagnostic requests, reported separately from production R requests, and never supply prices. `SEARCH_REDUCTION_TELEMETRY` changes diagnostic output only; successful assignments, candidate order, scheduling and termination on a hit are identical in both modes.

## 4. 声明窗口、根探针与 min-max DP

保留声明级 `k=1` 作者边。`k=2` 对每个声明至多追加一个统一的两层祖先候选，不枚举前提子集，不由跳边生成新窗口。新增候选数至多是批内活声明数；声明拆分不得改变窗口规则或生成额外选择自由。候选仍按 §3.2–3.4 作陈述级解析检验和定价。

两臂的根证书核验分别只持 `B_used` 和 `B_used∪S`。只有出现严格的上界差距时，基底根才追加一次完整 R；配对根不请求 NoHit。成功且经 kernel 复核时，将零价根超边加入两臂共享的候选图；边的前提是证书实际使用的事实，不能用无前提零边抹去 `S` 的成本。基底根探针成功直接提供 bind-only 证书。根探针和两层窗口候选探针仅在该臂闭合并经 kernel 复核时加入零价边；失败或耗尽不加边，不记一价。作者边仅在其实际 R 查询取得 Miss_R 后变为一价；Fault/NotRun 保持 unknown。已有 `R_v1` 成功证书也可支持 bind-only，`R_v1` 不必跑，其旧耗尽不成为新下界。

对种子 `v∈X`，`d_X(v)=0`。其余节点按入边候选取最小值：

```text
d_X(v) = min_e (c_X(e) + max_{u∈prem_X(e)} d_X(u))
```

空前提的最大值为零，无路为无穷。零价证书边只带实际使用的前提；正常耗尽的作者边带全部活的非种子前提。采用 min-max 深度，不对共享前提求和。生产图、DP、区间、回溯与 `classifyGraph` 属于非测试 Lean 核心，模型与生产复用。

深度是须先猜后验的构造层数。在完整 N 叉串行选择树、末端才可识别、最坏枚举序、无剪枝、无共享、无索引捷径和单位检查成本的明示模型中，固定深度 d 的枚举量为 Q_d(N)=Σ_{i≤d}N^i（N≥2），深度下降对应有效库宽 N 上的次数下降；N 是实际有效分支数，不是库条目总数。生产判官与该模型之间没有资源保持的对应，判官不陈述实际搜索时间、题目族增长阶或原问题复杂度。「节省无界」指差值最终超过任意常数，「深度降阶」指原深度趋于无穷且新深度为原深度的 little-o；时间降阶另须固定统一算法和完整成本模型。

未知作者边以 `[0,1]` 端点计算两臂 `[L_X(T),U_X(T)]`。下界将 unknown 边的前提置空，以允许将来的零证书仅使用原前提子集；上界保留作者边的全部前提。已认证的零边两端均只使用实际前提，已认证的一边两端均保留作者前提。含无穷时不相减；未决边只在阻碍严格区间分离时阻止阳性。必需的隔离、呈现、根否定和结构排除 incomplete 仍阻止阳性。保留最优路线回溯、证书实际前提及播种 `S` 的使用位置。

`SEARCH_REDUCTION_GIVEN_ABLATION=1` 启用 `d_given` 消融，向局部探针提供全部直接前提类型。未启用时只将已有 cut 零证书复用于 given 视图，其余保留区间，不报告完整消融比较。生产距离 `d_cut` 仍遵守合成前提隐藏规则。在共同图、假设单调的理想重建模型中 `d_cut≥d_given`。完整消融读数全等时报告“切式计价无可观测效应”，不把消融值带回生产判词。

## 5. 单源呈现与宽 `S` 排除

基底呈现认证只允许一条实际基底声明 `b`：完整陈述、∧ 投影或 ↔ 两向的有限视图，经带证书的正规化 `N` 后恢复整个 `T`。转换时把 `b` 当抽象假设，其他基底事实不得补实质分量；`b` 的证明只在最终恢复 `T` 时使用。多源组合交给局部重建与图，不充作单源呈现。

查询条件是非中性分量的有向包含 `A(T)⊆A(b)`，不要求键相等。冻结语法的索引必须完整，哈希只定位；跳过候选须有覆盖依据。中性分量是在共同 telescope 下不依赖源或基底、可由 `True`、`rfl` 或无前提 `omega` 闭合的分量，不进键。仿射项使用共同不透明原子字典正规化，算术证书只以单个源分量为前提；定义展开限于经检查的无环非递归别名。一般递归、matcher 和 recursor 保持不透明，归约预算耗尽不得伪装为未命中。索引、查询和证书构造均计预算。

宽 `S` 排除保留基底补分量、打包任一侧、算术、投影、双向恢复、依赖闭包藏目标及集合级拆分/打包的有限呈现检查，并包含单源呈现认证的命中。`S` 及其依赖闭包的分量联合能在 `N` 下直接恢复 `T` 时，不得以该集合制造收益；这不是任意 `S⊢T` 的全局搜索。

`S` 成员若至少有一个非中性分量，且实际匹配一条基底声明的单源呈现，则视同基底。全中性 `S` 不因空集包含而被拒，交给声明图判定；它仍须通过目标泄漏与活路径检查。

### 5.1 target-part 反向探针

The decision set follows the current paired optimum. After excluding a seed, the evaluator recomputes the selected route and probes newly selected seeds at most once. Final target-part completeness is checked against the final selected seeds; unresolved replacement-route seeds block a positive.

除宽排除外，若 `s` 与 `T` 在单射改名后互为陈述子项，或 `R_lookup` 持 `{T}∪B_used` 能闭合 `type(s)` 而只持 `B_used` 正常耗尽，则 `s` 是 target-part，不可作为新增结构种子。结构探针只为存在上界差距的配对最优路线所选 `S` 成员运行。独立探针可调用基底 R；反向探针先核验正证书，仅在懒决定集需要时追加完整 R，不认证配对臂边价。独立探针命中时无需反向否定；独立探针 NoHit 且反向证书命中时排除该种子。反向 R 完整 NoHit 时确定该种子不因反向推论而排除。独立探针未命中且反向证据未决时，target-part 排除仍为 incomplete，阻止阳性。成功须 kernel 复核；预算或故障具名 incomplete。该规则防止把真正依赖目标的等价泛化、拆分或重打包当作辅助线。基底已能独立闭合的 `s` 不因反向探针成功而排除，仍须经过单射改名与宽排除。

`T`、其别名/重述以及依赖它的声明不得偷偷进入配对环境。宽排除不因私有名、拆文件或声明包装失效。若 `S` 全为 target-part，不能判非 bind-only。例行可证的合成前提仍可因其陈述提供了隐去的信息而产生约化；防刷边界是 `T` 自身被基底根探针例行闭合时判 bind-only，读数必须保留其 R 和图作用域。

## 6. 发布判词与处置

发布判词为互斥的 `bind-only | reduction_R | no-gain_R | reject | incomplete`。内部三态 `Verdict` 保留既有模型与消费者接口，发布分类由 `classifyDisposition` 从 GraphReading 计算。

- `bind-only`：存在已核验的基底零价路线、呈现证书或既有参照成功。
- `reduction_R`：所有原守卫完成，图完整，基底根的 R Miss 已定价；两臂上界与基底下界有限，`L_B(T)>U_{B∪S}(T)`，且配对最优活路线实际使用合规 S 种子。报告两臂区间、closure 及 cut/proof_hard 见证。
- `no-gain_R`：守卫完成，并有有限数值证据 `U_B(T)≤L_{B∪S}(T)`。守卫超时不能产生此判词。
- `reject`：实际检出来源泄漏、重述或换装等拒绝证据。
- `incomplete`：未完成所需守卫或数值证据。输出唯一首要阻塞点（守卫名、查询或检查对、实际停点及补足方式），处置为「约化未获认证，不准入」，可并报区间。它不宣称未约化或无收益。

发布消费的任何一价记录为 searchKappa 或 coveragePrefixG 时，`basis=budget`，否则为 exhaustive；保守计算包括全部已定价作者边与所消费的基底根 Miss，不求最小依赖集。budget 读数仅用于带 R 版本与作用域的 Observe，不作为 CLAUDE.md §3.2 准入依据；exhaustive 也不自动取得 content 资格。`closure=zero` 只报告经装配核验的正证书零路线，partial 只说明所登记图的剩余构造层减少。

### 6.1 现在时限制

证书语法、命名重放、来源审计、图、DP 和分类由 Lean 执行；正证书经 kernel 核验，JSON 只作输出。unsafe 枚举器、磁盘索引完整性和预算记账属于运行时信任边界，标为 meta-computed，由命名重放与枚举器的差分测试及变异测试守护。`RuntimeBridge` 在 `ArmCompletion` 的连续编号、范围、共同轮数和实际支持模拟条件下证明生产 DP 的完成包络及阳性差距；条件定理保持条件形式，不声称端到端运行时健全性。Miss_R 是记录的冻结调度停点，exhaustive 才提供正常穷尽的守卫前提，均不是新增公理。Kernel 证明终态互斥、Option 价格、Fault/NotRun 无价、预算 Miss 不完成守卫、零路线依赖正证书以及固定图上 Hit 集合包含时各臂距离不增；零路线定理显式要求每条零价记录具有正证书。Kernel 只证明这些记录的分类及所列条件定理，不证明现实搜索穷尽、不证明没有其他显然证书，也不证明 unsafe 执行器与模型的端到端等价。`GraphModel.delta_not_monotone` 保留距离差不单调的边界。每个审计模块将 `GraphReading` 写成 Lean 数据，分别以 `classifyGraph reading = v := by decide` 及 A1/B 的 `classifyDisposition reading = d := by decide` 交 kernel 重算内部与发布判词。纯分类器的 `early_stop_verdict_eq` 要求分类状态相同；运行时提前停止与全量求值的一致性另作差分验收。完整分类器的基底证书单调性保持 open，部分信息精化可从 insufficient 转阳。未命中的非作者 shortcut 不进入当前下界图，其未来激活需要额外模拟依据。

距离下降不证明辅助结构难被发现；同一声明体内的重复引用在依赖去重后不计次数。本契约不主张 Frege / Extended Frege 分离，未发现获准证书也不表示不存在获准证书。

内联 `have` 不拆，声明体内部例行步骤与内部发明折成一个 `opaque` 步骤。两个见证打包进同一声明会折叠构造层，可能使约化消失而转为证据不足；本契约不宣称任意 helper 拆并保持距离，也不要求为了读数制造辅助声明。

图外短路线可能消除图上的正差；猜测型绕路也可能抬高作者路线距离。窗口不能覆盖所有替代证明。声明粒度与证明项粒度的距离无统一大小关系，不能宣称互为上下界。

在假设单调的模型中，增加种子不增每臂距离；增强 R 也不增每臂距离，bind-only 对 R 增强向上单调。实际固定预算过程须另核验该前提，不能从预算 Miss 推出穷尽或搜索过程本身的单调性。

距离差 `Δ` 对 R 增强不单调。例如 `B={b}`、`S={s}`，`b→s`、`b→t`、`s→t` 初始代价均为一时 `Δ=0`；只把 `s→t` 降为零可使 `Δ=1`，再把 `b→t` 降为零又使 `Δ=0`。重建者强度的单调方向由 bind-only 的单调性承担，不能替换成 `Δ` 单调。

## 7. AURIC FIB 与 ATOM 假设

AURIC 不提供 P 侧边价，也不改变 P 侧判词。实际 `LawFact.separated` 给出 `strict`，`LawFact.identifiable` 给出 `collapsed`，均未取得则 `unknown`。同族同域 strict 与 collapsed 互斥，三态穷尽；正宽度、正 `Δ` 或单点数值不能代替 LawFact。这里 FIB 的 `Δ=rκ−XY` 与图距离差是不同读数。

有限候选域双前提模型只提供单向桥：数据元变量不共享、计数律为积律且 `z=0` 时，`Pyramid.delta≡0` 并可得 collapsed；同一族内若存在边际相同、联合坐标不同的两个可实现耦合，且所需四格质量为正，则得到 strict。变量共享或四格非空本身不保证存在这样的两个耦合。逆命题不成立：常值律可 collapsed 而 `Δ>0`，strict 的二点族也可在常数规模枚举，不能推出搜索下界。既有观察的后处理和常量身份元数据不切开观察纤维；完整状态身份能否切开须另证。

FIB 五模式单元刻画两个选择的耦合，不刻画是否存在选择。任意两个布尔特征配任意测度，取 `z≡0`、`r=1` 即可表示五模式律；任意超边二元化本身也不提供难度信息。因此“所有证明可拆成 FIB ATOM”的无约束全称形式不作定价或判词依据，`c=1⇔共享数据元变量(strict)` 也不是契约。

计算面中的合法角色限于上述单向模型桥、猜测边上的静态 `coupled/independent` 注记，以及预登记的 `shared_data × c` 交叉表。它们不引入新的 LawFamily/Application 适配器或 FIB 来源定理。作者另可按 §7.1 提交既有合同表达的信息面证据。

静态注记只读取消费者陈述的逻辑骨架：经可约头正规化后，若一个 `Exists` 的非证明见证变量同时出现在其作用域内某个 `And` 的两侧，则 `shared_data=true`、`coupled`；否则为 `false`、`independent`。递归范围是 `forall`、`Exists`、`And` 和 `Or`；外层已给定参数不作为待选见证。`independent` 只表示该骨架未检出共享，不声称任意隐藏谓词、切式或证明实现语义独立，更不构成 strict/collapsed 证书。读取失败为 unknown；该注记不参与定价、种子排除或判词。

交叉表的总体、注记定义和夹具预测须在运行前登记。表按基底臂候选边的 `shared_data∈{false,true}` 与 `c∈{0,1}` 计数，明确包含作者边、两层窗口候选和根探针边；unknown 价和缺少注记分别报告，不填入任一布尔单元。`d_cut/d_given`、无辅助声明数与 opaque 声明数随同报告。

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
2. R 对假设单调时，扩大种子不增距离。若 `d_X(v)=0`，且 `v` 对所有候选消费者（含根探针与两层窗口候选）都是解析前提，加入 `v` 不改变可见假设和定价，因而不改变任意 `w` 的距离；若 `v∈X`，加入它也不改变距离。无条件的零种子冗余不成立：存在零价可得的合成前提，在播种后使另一条边从一变零并使目标距离严格下降。
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
- `doubledContent ← addition` 的预测为基底区间包含于 `[1,4]`、配对区间 `[0,0]`、严格区间下降、non-bind-only、`closure=zero`；四是完整作者路线的上界，不要求惰性否定将基底区间压成单点。`Lean.Omega.*` 只作叶或不出现；替换 `addition` 内部闭合器不改变该声明图读数。若根探针直接闭合 `T`，如实判 bind-only。
- `squareVia := ⟨42,squareFact⟩` 的预测为一到零、zero，`squareFact` 是合成前提且自身不被误记为难；真实依赖它的两层链预测为基底区间包含二、配对区间包含一、严格区间下降、non-bind-only、partial。按 §3.5、§4，配对边不运行完整否定，不能要求配对下界精确为一。`sharedWitness` 的两臂区间均包含一且包含于 `[0,1]`，判 insufficient、无 closure；两臂上界相等时不要求基底完整否定。`S` 必须出现在作者证明的活依赖中，只有作用域可见不算。
- 每条 `DECL_PREDICTION` 都是编译断言；值为 false 时抛出 Lean 错误，标准测试门非零退出。固定 false 用例核对该拒绝行为。
- unwrapped、splitHelper、specialized、package、dead、等价泛化及目标本身例行的 `routineVia` 夹具均不得判非 bind-only；单独知道某个合成辅助陈述例行可证不构成排除理由。单源呈现、宽 `S` 排除、全中性 `S`、私有名与词汇传输回归保留；判词变化逐项说明适用规则。
- 登记声明逐条报告是否越过词汇阶段、顶点和边数、合成前提数、两臂区间、判词、closure、unknown 原因、见证边、耗时与整棵进程树的物理 footprint 峰值。
- 同时报告 `d_cut/d_given`、`shared_data × c` 交叉表、“无辅助声明”数量与 opaque 声明数量。切式消融全等时如实报告无可观测效应。

## 10. 资源边界

顶点数不超过活闭包内批内声明数加 `|B_used|`。每臂每顶点至多两次声明探针，另有两次根探针、每个 `S` 成员至多一次反向探针和一次基底独立探针，每次探针的旧局部路线分配 `200000` 搜索心跳；查表按 §3.4 为每候选分配 κ = `200000` 搜索心跳与 `8000000` 准备心跳，每查询另受覆盖上界 G = `340000000` 约束。R 的 κ/G 截断按 Miss_R 定价；守卫超限与执行 Fault 保留 incomplete，不授予约化。没有证明项顶点容量扩容或子项义务搜索路径。

内存包含一份共享不可变基底导入，加 `O(Σ|type(v)|+|前提|)` 的当前目标数据；证明体仅线性遍历取依赖，消费者不对全环境建树。完整路由 manifest 在堆上驻留，答案缓存与断点的 compacted regions 保留至进程退出；当前实现没有任意长批次跨目标常驻量的严格上界。探针串行执行，整棵进程树物理 footprint 受 `12 GiB` 基础设施守卫约束；触发该守卫或挂钟截止时中断运行并记录 interrupted，不把基础设施中断计入 R 的语义判词。导入环境的基础驻留另行实测，不能冒称与库大小无关。

## 11. 与现行准入的关系

本契约只提供搜索约化的 Observe 读数，不替换 `CLAUDE.md` §3.2 的判形、活路径、有消费辅助声明、模块准入依据或开放问题结算规则，不替代 §3.3 用途规则、§3.9 四槽义务和 AURIC 来源绑定。把带作用域的 non-bind-only 升级为 §3.2 content 或修改该条，必须另获 owner 裁决；模型定理、实现通过与校准读数都不能代替。

“只要能写出 Lean 代码就是非 bind-only”会把别名和薄包装当成新内容；无界地把已证明结论全部免费提供又会使 content 为空。本契约固定有限图和可复现重建者，把“变容易”落实为声明辅助构造层数之差，并保留证据不足、作用域和未决边界。


### 9.1 热延迟与对照数据域

同一最终 head、索引数据域、请求和冻结证书池上，A1 为逐检查计额加 v18 价格映射，B 为相同查询记录的 v19 价格映射。历史 A0 不改写。数据域保存逐文件输入清单与声明清单；不同指纹的负记录不复用。

热序列固定为同机串行 `F0,H1,F1,H2,F2,H3,F3`，通过条件为 `median(H1..H3) ≤ median(F0..F3)+30 s`，偶数中位数取中间两值的均值。F 是登记 sha256 的固定开销请求，走同样的启动、导入与核验路径。请求定义改变后与历史固定开销不可比。每次 H 断言整次认证缓存命中且新增 R 搜索为零；报告全部原始样本、最慢值与负载，不删除慢样本或重复选优。

内部兼容接口的基底根 `Run.exhausted` 表示已定价的 Miss_R；只有结构化 `RQuery.guardRun` 的 exhausted 表示可供守卫消费的穷尽。两者不得互换。新阴性校准须记录实际 κ/G/Fault/NotRun 停点；未触发预定停点时报告覆盖缺口，不能改变预期。边界注入回归不替代真实生产候选人口的防假阳性校准。
