# 仓库 Harness 的形式模型 v0.2(勘误)

**状态**:提案,非现役律法。本文件是 `docs/reports/` 下的 `kind=data` 工件,不承担任何门的权威;
凡与 `docs/develop/spec/golden-ledger-repo-spec.md` 或 `CLAUDE.md` 冲突处,以后二者为准。

**读数与实现结论基线**:除另注明外,全部取自 `trureturing@25c3a9716`,采集命令与出处逐条内联。
tracked 文件数 29,407 属于 `94f64f416`;`25c3a9716` 的实测值为 29,469,本文的压缩比据后者计算。
**产地**(第 9′ 条):`/consensus-rnd:sshx` skill;六席思考面板为 5× codex-cli
(teleology / parsimony / fidelity / natural-ownership / proportional-containment)
+ 1× nyxid-oracle(worth),判词分布 `reject 2 / revise 4`。`worth` 席 attempt 1 因
`extraction_failure` abstained,attempt 2 完成。五席属于同一载体族,不得声称模型多样性;
所有读数由 orchestrator 亲验,或由席位独立复算后再经 orchestrator 复核。

---

## §0 判据 —— 这份模型什么时候算错

本模型下注三条可证伪的命题。任一被证伪,模型即须改写而非打补丁:

- **P1(本仓分类闭合)**:`trureturing@25c3a9716` 的受管字节可由三个正交轴唯一定位;
  跨仓推广只保留为带前提的条件命题,且尚未在第二个仓库验证(§8、§10-e)。
- **P2(规则派生)**:改动规则是 `(权威, τ)` 的函数,不是逐工件声明的自由文本。若某工件必须写一条只适用于它自己的规则,P2 被证伪。
- **P3(带前提的充分条件)**:在 artifact universe 稳定、`dep` 可靠且稳定并持有覆盖候选态实际读集的跨步证书、judge 与 producer
  均 deterministic/hermetic、基例证书已建立时,强化不变量或改动已声明的全局参数,均足以触发全量重验;
  此二者不再声称穷尽所有触发。
  **2026-08-26 被证伪的是原 P3(v0.1「恰有两种」的充要/穷尽形,见 §5),不是本条当前 P3。**
  当前 P3 是改写后成立的带前提充分条件,仍待实例化检验。

不下注的部分明写为 `open`(§10),不用语气代替读数。

---

## §1 基本对象与分型关系

**仓库状态** `R`:git tree,即有限的内容寻址映射 `path ↦ blob`。历史 `R₀ →^δ₁ R₁ →^δ₂ ⋯`,每步一个提交。
本模型全部依赖 git 的一条性质:**未被 δ 触碰的路径,其字节在 R 与 R⊕δ 中逐字节相同**。§5 的归纳全压在这一条上。

**工件** `x ∈ A(R)`:**不等于文件**。工件是 harness 能对其说 admit/reject 的最小单位。
本仓的粒度实测是三种并存:路径(FILEMAP)、Lean 声明(GID)、账本事件(frozen ledger event)。
故 `A` 上有一个字节区间映射 `loc: A → 2^bytes`,工件按 `loc` 成森林。**粒度是旋钮,不是给定**(见 §2 粒度律)。

读取关系必须按发生阶段分型;生产时读取、运行时读取与判定不能压成同一个 `I`。本模型使用以下原语:

| 记号 | 名 | 含义 | 本仓现状 |
|---|---|---|---|
| `π(x)` | producer actor | `π:A(R)→ProducerActor∪{⊥}`;`⊥` 表示手写 | FILEMAP `produced_by` actor 名 |
| `I_run(y)` | runtime inputs | `A(R) → 2^A(R)`;工件 `y` **执行时**读取的工件闭包 | **未声明**;`.NET` 工程判者仅有静态上近似 |
| `I_prod(x)` | production inputs | 部分映射 `A(R) ⇀ 2^A(R)`;生产 `x` 时的读取闭包 | **未声明**;`EngineeringInputDeriver` 不派生此关系 |
| `J_{D,K}(x)` | typed judges | 对象域 `D` 到判者域 `K` 的定型判定关系 | `V_path ⊆ Selector × VerifierActor`;`J_component ⊆ Component × Component`,二者不合并 |
| `C(x)` | consumers | `A(R) → 2^(A(R) ∪ ProgramActorWords)`;执行时消费 `x` 的对象 | FILEMAP `consumed_by` 近似承载,并含仓外 actor |

**producer actor 解析**:定义部分映射 `resolve_R:ProducerActor ⇀ A(R)`,只在 actor 能唯一解析到 `R` 中受治理的可执行工件时有定义。
`π(x)=⊥` 时 `I_prod,R(x)=∅`;`resolve_R(π(x))` 有定义时 `I_prod,R(x)=I_run,R(resolve_R(π(x)))`;
其余情况 `I_prod,R(x)` 未定义并记 `open`,不得用于投影分类。对每个判者域 `K` 另记定型读集
`JudgeReads_R^K:K→2^A(R)`;`K=A(R)` 时它就是 `I_run,R`,actor 域不得用空集冒充。

**定义(消费边,工件定型子域)**:`C := I_run⁻¹`,即 `∀ x,y ∈ A(R). y ∈ C(x) ⟺ x ∈ I_run(y)`。
**这一行按定义恒真,不含内容**,不是可以假设或违反的东西。有内容的是它的**一致性谓词**:
`ConsumerConform(R) := (FILEMAP.consumed_by(x) ∩ A(R)) = I_run⁻¹(x)` ——
登记表**声明**的消费边是否等于从 `I_run` **派生**的消费边。那是**可查的**,可以为假;为假即仓库的缺陷。
`C` 与 `I_run` 在该子域上是同一条**消费边**的两个方向;落在 `ProgramActorWords` 上的消费边属于
另一个对象域,不参与互逆律,因而不会要求无类型的 `I_run(agent)`。`I_prod` 只在上述 `resolve_R` 有定义处组合;
`J_{D,K}` 是按两端对象域定型的**判定边**,与消费边不同型。下文抽象地写 `J_{D,K}` 时一次只取一个载体;
本仓 `V_path` 与 `J_component` 不构成单一 `J`。**投影分类只能使用有定义的 `I_prod`。**

原式按原定义为假。反例是判者 `test` 执行时读取被测 `impl`,故 `test ∈ C(impl)`;
但手写 `test` 满足 `π(test)=⊥`,于是 `I_prod(test)=∅`,`impl ∉ I_prod(test)`。
同一反例适用于任何运行时读取别的工件、但自身为手写的可执行物。

另有实现层类型差距:`Meta/FILEMAP.toml` 当前 `consumed_by` 的元素常是仓外 actor,
并非 `A(R)` 中的工件;例如 `docs/reports/**` 明写 `agent`。因此该字段当前实际近似为
`A(R) → 2^(A(R) ∪ ProgramActorWords)`,不能未经分域就当作 `A(R)` 上的自关系。


**诚实分栏。** 本文不声明 Lean `axiom`,但承重句子并不穷尽于定义、谓词和定理三类:

| 类 | 是什么 | 它的义务 |
|---|---|---|
| **定义** | `C := I_run⁻¹`、`I_prod := I_run ∘ resolve_R ∘ π`、`τ := height(J_component)` | 无义务,只要前后一致 |
| **谓词** | `WellGoverned` / `Registered` / `RefIntegrity` / `ConsumerConform` | 义务是**去查**;可以为假,为假即仓库的缺陷 |
| **带假设的定理/命题** | 2.1 塔终止、5.1 增量可靠性、5.2 三种可靠修法、6.1/6.2 判者两重义务 | 义务是**在写明的假设下成立** |
| **外部契约/假设** | 未触碰路径的 git tree 字节保持、判者与 producer 的 hermetic/deterministic 条件 | 由构造者或外部系统提供;本文不能在模型内证明 |
| **规范性政策/设计选择** | 投影不设门、准入判者从 base 解析、粒度与成本的治理选择 | 必须指向权威裁决,不得伪装成本文推导出的定理 |
| **实例与测量义务** | 具体路径、提交、actor、当前计数、§9 指标与 §10 `open` | 逐项实测或诚实标未测;不进入抽象定理 |

**为什么这个区分承重,而不只是命名洁癖**:把一个**可查的谓词**写成公理,等于
**把一个本该红的检查藏成一个前提**。本文 v0.2 就犯过这个错——原文写「本仓不满足公理 2」,
而**一个不被满足的公理是矛盾**;真实情况只是准入实现与其签名不符,是符合性缺口。
措辞错了,连带把「该去修实现」误导成「该去论证前提」。

§1 开头那条 git 性质(未被 δ 触碰的路径,其字节在 `R` 与 `R⊕δ` 中逐字节相同)
属于上表的外部契约,不在模型内可证。但在形式化落地时它仍**不该写成全局 `axiom`**,
而应是 `GitTree` 结构体的一个**字段**——由构造者提供并承担,而不是被全局假设。

---

## §2 程序/数据是边上的角色,不是节点的属性

用户直觉的精确形式:**「是程序还是数据」不是 `x` 的属性,而是边 `x → y` 的角色。**

对每条同域边 `j → x`(`j ∈ J_{D,D}(x)`)或已解析的 producer 边
`resolve_R(π(x)) → x`:左端是**程序**,右端是**数据**。同一份字节可在一条边上是程序、
在另一条边上是数据。测试代码判定实现,故 `test → impl`:测试是程序,实现是它的数据。
而**谁判定测试?** 变异运行器 `m`:`m` 把测试当数据,把实现当扰动源。故 `m → test → impl` 是一条链,不是环。

> **变异证明不是纪律,是本模型的强制推论**:`test ∈ J_{A,A}(impl)` 一旦成立,`J_{A,A}(test)` 就必须非空,
> 否则 test 是一个无人判定的判者(§6)。变异运行器是 `J_{A,A}(test)` 的规范居民。

**谓词(治理无环,按域定型)**:先定义部分关系
`Π_D = {(a,x) : x∈D, π(x)≠⊥, resolve_R(π(x))=a, a∈D}`。只有每个 `x∈D` 的非 `⊥`
producer actor 都唯一解析到 `D` 中的工件时,`Π_D` 才有定义;任一 actor 未解析、非唯一解析或解析到域外时,
`Π_D` 保持未定义且 `WellGoverned_D(R)` fail-closed 为假,不得把该 producer 当作空边省略。
在 `Π_D` 有定义时,`WellGoverned_D(R) := Acyclic(J_{D,D} ∪ Π_D)`。不同载体未经定型注入不得作无类型的并集;
特别地,本仓 `V_path` 不与 `J_component` 相并。等价说法:没有工件参与决定它自己的准入。
**这是一个谓词,不是公理**:某个具体的 `J` 有没有这性质是事实问题,须去查。
`τ` 正是**在该谓词成立的前提下**由良基递归定义;谓词不成立时 `τ` 未定义,而不是「公理被违反」。
旧稿曾声称 `J_{D,D}` 中有环就使 `H=F(H)` 有多个不动点且恒含「全部 admit」,这是假的:
一节点环配常拒绝算子 `F(H)=reject` 时只有「全部 reject」一个不动点。环能阻断良基递归,但仅凭有环
不能推出不动点的数量或内容。候选提交 `return Accepted` 的风险由下面的跨版本准入签名刻画,不再借该错误断言论证。

**签名(信任定向)**:准入函数的型即 `H : (base : R) → (δ : Delta) → Verdict` ——
判定候选 `R'` 时,**每个判者在 `R` 中解析**是这个型的内容,不是附加的假设。
上一条谓词是树内的无环,这个签名是跨版本的无环。只有前者成立时,候选仍可用「自己带来的判者」
判自己——图上无环,历史上有环。

> **本仓实测**:`.github/workflows/ci.yml:749` 的步骤名即 `Run the harness gate with the candidate's own judge`;
> 同 job 的 `:715 Resolve judge binary content address before build outputs exist` + `:724 Restore judge binaries`
> 表明判者二进制按**候选源码的内容地址**取缓存,未命中即由候选自行构建。
> CLAUDE.md 第 19 条明记 base「不 checkout、不编译」。**故本仓的 `J_component` 满足 `WellGoverned`,而其准入实现与上述签名不符**
(一个「不被满足的公理」是矛盾;这里的真实情况是实现与型不符,即符合性缺口);
> 缺口当前由 `pull_request_target` 的 workflow 文本取自 base 侧 + rc=3 元层脚手架承担,
> CLAUDE.md 自己称其为「记录在案的 bootstrap 脚手架」。本模型的立场:这是**已知负债**,不是设计,记 `open`(§10-a)。

**信任地层 τ**:`τ: Component → ℕ` 仅由组件判定边 `J_component` 派生,**永不声明**;`V_path` 不参与 `τ`。
```
τ(c) = 0                                   若 J_component(c) = ∅ 且 c 是信任根
τ(c) = 1 + max{ τ(j) : j ∈ J_component(c) } 否则
```
组件判者的 τ 严格小于被判组件。下文对工件写 `τ(x)` 时,仅是其唯一治理组件 `c_x` 的 `τ(c_x)` 简写;
该组件无法唯一解析时 fail-closed。内容组件坐在 τ_max。**τ 是组件判定图的高度函数,不是任意拓扑序号,也不是入度**
(CLAUDE.md 第〇节已禁与证明深度 depth(v) 混用;二者相关而不同构)。

**定理 2.1(塔必有顶,顶不可自证)**:`J_component` 有限且无环 ⟹ 组件判者链终止。
终点不能是「一个没有任何东西判定它的测试」——无人判定的判者与不存在的判者在观测上等价(§6)。
故终点必是信任根 `τ=0`,其可信来自**内容寻址 + 公开可独立复验**,而非任何判者的背书;其自身一致性标 `open`。

> **本仓实测**:`tools/TOWER.yaml` 末节 `bootstrap: id: bootstrap-pr-1, judge: open,
> reason: "Godel boundary: the bootstrap trust root cannot prove its own consistency",
> genesis_event: sha256:80bdd2d2…, verification: ASSUMED-UNVERIFIED`。塔顶已诚实标 open。

**粒度律(定理 2.2)**:登记表的**分辨率应与 τ 成反比**。
错误代价按 `C(τ) = C_leaf · α^(τ_max−τ)` 增长,而分辨率的价值正比于该层单次错误的代价。
故靠近信任根处按文件甚至按符号登记,叶子处按 glob 登记。

> **本仓实测**:TOWER 16 个组件中,`content-artifacts` 一个节点吞下全部内容类(F/B/E/C/L/P/Meta/…),
> 而 harness 侧铺开 10 个 `repository-files` 组件。**这不是粗糙,是符合粒度律的**。
> 反过来,FILEMAP 用 63 条 pattern 覆盖 29,469 个 tracked 文件(`git ls-tree -r --name-only 25c3a9716 | wc -l`),
> 压缩比约 468:1,也在叶子端符合本律。两个表各自的分辨率都对;其对象域不同,
> 不能仅因两表并存就判为同一事实的两个真源(§7)。

---

## §3 三个正交轴,而不是一个 `kind`

本仓 FILEMAP 的 `kind` 现有 5 个取值(program 28 / data 20 / generated 8 / ledger 5 / truth 2),
把两件不同的事压进一个字段:`program` vs `data` 是**边上的角色**(§2,相对的),
`generated` vs `ledger` vs `truth` 是**权威来源**(绝对的)。混轴的代价是二者都无法机器判。拆开:

**轴 A —— 权威(真值住在哪里)**

| 取值 | 定义 | 判据 |
|---|---|---|
| `root` | τ=0,信任注入点 | 内容寻址且公开可独立复验;一致性标 open |
| `source` | 手写;`π=⊥`;字节本身即真值 | 无 producer,且承担独立权威 |
| `ledger` | source + 单调性约束(append-only) | 承担**历史权威**:它断言「当时发生了什么」 |
| `projection` | `I_prod(x)` 有定义,且解析后的 producer 以该闭包重发可逐字节得到 `x` | 四项合取,见下 |

**投影四项合取**(CLAUDE.md 第〇节原文,此处只作形式化):
① `π(x)` 受 harness 治理;② `I_prod(x)` **完整声明**且受治理且保留;
③ 可由 `π(x)` 与 `I_prod(x)` 逐字节无损重建;
④ 无独立权威(不承担 policy/oracle/history authority)。四项全真才是投影;未知或外部依赖 fail-closed 判为非投影。

**仓库政策(投影不设门)**:四项合取判为 `projection` 后,不对投影本身设置准入门。此规则由
`CLAUDE.md` 第〇节的**规范性裁决**直接授权,不是本文从成本读数推导出的定理。该裁决记录的理由包括:
守投影会长出冲突分类器、自动重算链、FIFO 租约;
实测 `pr-shepherd` 一族 shell **2,817 行** + 专职测试 **3,913 行**,其 85 个测试是 CI test 阶段最慢的
**≈396s**;另有 `conservative` **529s/次**、`c0-renew` **24 min/次**。这些读数是该规范性裁决的理由,
不是本文对「门数为 0」的推导。

- **字节一致性验算**:`x` 与解析后 producer 基于 `I_prod(x)` 的重发结果比对,能抓陈旧副本、手改及非确定性差异;
  它只验投影四项合取的第三项,不构成治理、不构成准入义务,不得据此为投影设门。
- **producer 语义判定**:重算不能抓确定性 producer bug;该语义判者应作用于 producer 与规格,而非给投影 `x` 设门。

「施于投影的门不增加信息」能否得到非空洞形式陈述,记为 `open`(§10-g),不再冒充定理。
> **现状读数**:63 条 FILEMAP 条目中 8 条 `verified_by=produced_by`;其中 6 条 `run-local`,2 条仍 tracked:
> `Blueprint/**/*.md` 与 `Evidence/D5/values.json`(开放违例 `D5-T0031`)。这只描述同名验算,不构成政策依据。

**轴 B —— 角色**(§2,per-edge;节点级摘要):`judge`(出现在某个 `J_{D,K}(y)` 中)/
`producer`(存在 `y`,使 `resolve_R(π(y))=x`)/ `inert`(叶)。未解析的 producer actor 不会使任何工件节点成为
`producer`;需要该边的分类保持未定义并 fail-closed,不得把未解析当作没有 producer 边。

**轴 C —— 居所**:`committed` / `run-local` / `external`。本仓已有(`runtime_disposition`,52/6/5 分布)。

**定理 3.2(改动规则是派生的,不是声明的)** —— 即 P2。规则表恰好是轴 A × τ 的函数:

| 权威 | 可否手改 | 准入义务 | 单次改动代价 |
|---|---|---|---|
| `projection` | 手改不承权威;应重新发射 | 四项合取分类 + CLAUDE.md 第〇节规范性裁决:无门;重算只验第三项 | 0,重新发射 |
| `source` | 自由 | 其 base-解析的判者 `J_{D,K}(x)` 全部 admit | `C(τ)` |
| `ledger` | **只许追加** | 后缀扩展检查 + 写入门作用于新增条目 | `C(τ)` / 条 |
| `root` | 可,但贵 | 保守扩展证明 + 独立对抗评审 + 账本留痕 | `α^{τ_max}` |

**这就是「准入、改动规则很复杂」的收口**:复杂度是假的。规则只有四行;
看起来复杂是因为规则当前被写成了逐工件的自由文本(35 个 `verified_by` 名字、10 个 `judged_by` 名字),
而不是这四行的实例化。**若某工件必须写一条只适用于它自己的规则,那不是规则,是代表元**(CLAUDE.md 商余结构)。

---

## §4 登记律 —— 「不会莫名其妙多出来没有消费者的东西」

**谓词(全量登记 / 双射)**:`Registered(R) := dom(Reg) ≃ tracked(R)`(selector 粒度双射,两向 fail-closed)。登记表 `Reg` 本身是工件。

> **本仓实测:已满足。** `tools/StrataLint.Cli/Commands/FileMap/FileMapPolicy.cs:520`
> `"tracked repository file matches no FILEMAP pattern"`,`:548`
> `"non-run-local FILEMAP pattern matches no tracked repository path"`。两个方向都红。
> **这是本仓最强的一件机器**,用户想要的「出现即登记」在文件粒度上已经成立。

**谓词(按域的引用完整性:全称,不是存在)**:`RefIntegrity(R) := ∀ n ∈ names(Reg), resolves(n)`,逐项展开为——`π` 的非 `⊥` 名须解析到 `ProducerActor`,使用 `I_prod` 时还须有
`resolve_R(π(x))∈A(R)`;`I_run` 的参数和值须在 `A(R)`;每个 `J_{D,K}` 的对象与判者须分别解析到 `D` 与 `K`;
`C` 的工件引用须解析到 `A(R)`,仓外消费 actor 则须属于闭字母表 `ProgramActorWords`。逐名检查,不得对条目做存在量化。

> **本仓判例(源码自记)**:`FileMapPolicy.cs` 的中文注记记着 #1116——
> `kind=data` 的 `verified_by` 曾只检查「至少有一个真 verifier」(`.Any(...)`),
> 于是 `emit-check` 目标被删后,`Library/*/*.md` 仍写着它而永不变红,因为同条目里 `LibraryNoteCatalog` 还活着。
> **这是量词 bug,不是疏忽**:`∃` 让登记表可以静默腐烂。现已改为逐名。

**可选的 GC 存活性(未被本仓采纳)**:若另案决定把存活性定义成消费图可达性,可令
`live(x)` ⟺ `x` 从显式根集可达,根集再区分对外交付物、信任根与活工件的判者;
`dead(x)=¬live(x)`。这是一项额外的 GC 工件标准,不是仓库现行标准。

**条件命题 4.1**:若采纳上述 GC 可达性,则仓外 actor 不能未经建模就充当 `A(R)` 内的可达边;
要判 `deliverable` 与死工件,必须给导出边界或等价的类型化根语义。该条件命题不推出
「消费者非工件 ⟹ 当前缺陷」。

> **本仓实测(29%,非缺陷)**:63 条中 **18 条的消费者全部**取自
> `{reader, developer, agent, automation}`。这四个词在 `FileMapPolicy.ProgramActorWords` 中是
> deliberate 的闭字母表成员,仓库合法放行;它们不指向 `A(R)` 中的工件。
> 以下均为 FILEMAP **selector**,不是 tree object 引用:`*.json`、`AGENTS.md`、`CLAUDE.md`、
> `Evidence/D5/values.json`、`Makefile`、`README.md`、`agents/**`、
> `docs/CONTRIBUTING.md`、`docs/GOVERNANCE.md`、`docs/reports/**`、`skills/**`、`tools/ARCHITECTURE.md`、
> `tools/Architecture/HARDCODE-LEDGER.md`、`tools/Makefile`、`tools/scripts/**`。
> 另三个 selector 条目为 `pattern = "Generated/DAG.md"`、`pattern = "Generated/FILEMAP.md"`、
> `pattern = "Generated/echo-residuals/*.md"`;其 `runtime_disposition = "run-local"`,按声明本就不在 git 索引。
> `Meta/FILEMAP.toml:407-411` 对 `docs/reports/**` 明文规定 `consumed_by = ["agent"]`,
> 直接证明这是现行 spec 的合法形,不是遗漏。

若未来要把存活性做成可判的可达性,则需要区分 `deliverable` 与死工件,并为仓外 actor 定义进入根集的语义;
当前仓库没有主张要做这件事。故它是**未被采纳的设计要求**,不是现状差距或缺陷。

---

## §5 准入 = 归纳步 —— 全量 / 增量的条件边界

harness 真正声称的东西是 `∀i. P(Rᵢ)`,`P` 是若干谓词的合取。建立它只有两条路:

- **重验**:每步重算 `P(Rᵢ)`,代价 `O(|R|)` / 步。
- **归纳**:一次性证 `P(R₀)`(基例),然后每步证 `P(R) ∧ step(δ) ⟹ P(R ⊕ δ)`,代价 `O(|δ|)`。

**定义(局部谓词)**:令 `d ▷_R x` 表示定型对象 `d∈D` 直接命名、选择或治理工件 `x`;`D=A(R)` 时 `d=x`。
对执行 `ψ` 的**全部**判者域定义
`ActualReads_R(ψ,x)=⋃_{(D,K)∈Domains(ψ)}⋃_{d▷_R x}⋃_{j∈J^ψ_{D,K}(d)} JudgeReads_R^K(j)`。
故 `V_path` 的 `Selector × VerifierActor` 分支与 `J_component` 分支都在并集内,不得被 `J_{A,A}` 吞掉或省略。
`ψ` 在 `R` 局部 ⟺ `ψ(x)` 只由 `x ∪ ActualReads_R(ψ,x)` 的字节决定。机器使用跨步静态闭包
`dep̂_{R→R⊕δ}`,它必须覆盖上述全域并集,不能只因名称相同就视为相等。

**实例化证书义务(跨步)**:对每个继承工件 `x`,必须证明
`ActualReads_R(ψ,x) ∪ ActualReads_{R⊕δ}(ψ,x) ⊆ dep̂_{R→R⊕δ}(x)`;候选态实际读集也在量词内。
新工件归入 `δ` 并必查。`dep̂` 必须是该步两态运行时实际读取集的可靠上近似,而不只是基线态上
「登记表可算」的某个集合。派生失败、结果非法或不完整时,机器**不得**给出 `proven-disjoint`,必须回落全量。

**定理 5.1(带跨步可靠上近似前提的增量可靠性)**:若 `P` 的每个合取项在两态均局部,且上述跨步证书成立,
则只检查 `touched(δ) = δ ∪ { y : dep̂_{R→R⊕δ}(y) ∩ δ ≠ ∅ }` 即充分。
> 证明:对 `x ∉ touched(δ)`,两态的 `x` 及实际读集都落在未被 `δ` 触碰的同一闭包内,
> 故其字节逐字节相同(git 性质);`ψ` 是这些字节的函数;归纳假设给出 `ψ(x)` 在 R 中成立。∎

> **席位间分歧与调和**:两席判原条件式本身成立,因为「`ψ` 只由 `x ∪ dep(x)` 的字节决定」
> 在语义上已经蕴含依赖完备性,漏洞在可执行证书而非条件证明;一席判原表述不成立,
> 因为「登记表可算」不蕴含「可靠」。二者可调和:**条件式无误,缺的是实例化时的证书义务**。

> **条件推论**:只有局部性与覆盖候选态实际读集的跨步证书均成立时,才可对未触碰的 `x` 增量跳过。
> 基线态证书不能独自授权跳过,也不能把该条件结论扩张成无条件禁令。

**定理 5.2(非局部谓词的三种可靠修法)**:聚合式谓词(计数、唯一性、跨文件 join、全局 schema 版本断言)非局部,
增量检查不可靠。以下三种是可靠修法,但不构成穷尽枚举;全量重验本身也是可靠处置:
1. **摘要化**:引入可增量更新的摘要 `S`,`S(R⊕δ) = u(S(R), δ)`,改查导数。代价:多一个工件及其自身的一致性义务。
2. **降级到检测层**:移出准入,改为合并后巡检 + 勘误。**仅当违例可逆时合法**(CLAUDE.md 第 20 条分级)。
3. **容差带**:对单调有界聚合(`count ≤ B`),准入判 `count(R⊕δ) ≤ B − (w−1)·k`,
   其中 `w` = 合并并发宽度,`k` = 单 PR 最大增量。

**本轮第十项处置(E10)**:v0.1 以被 CLAUDE.md 第Ⅵ节「禁模糊措辞代替测量」禁止的「很可能」
声称目录容差带足够;`w` 未测,故本轮保留弱化后的条件结论,不再声称当前带宽足够。

> **本仓实测(定理 5.2 的第 2+3 混合形,且推导与仓内注释独立一致)**:
> `tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs:73` `DirectoryFileLimit = 12`(准入,局部:只判被碰目录),
> `:85` `DirectoryToleranceLimit = 24`(全仓网,带宽 12)。
> 该常量上方的英文注释独立写出了同一条论证:两个从同一 base 分叉的 PR 各向 11 文件的桶加一个,
> 各自看到 12 都放行,并集 13 让全仓扫描变红并堵死所有无关 PR——「that is what made strict load-bearing」。
> **本模型给出该带宽的定量判据**:带宽 `≥ (w−1)·k`。此处 `k=1`,带宽 12 ⟹ **对 `w ≤ 13` 可靠**。
> `w`(实际并发宽度)**本轮未测**;CLAUDE.md 记 dev 每小时前进约 16 提交,故 `w` 值得实测(§10-c)。
> 这是本模型对现役机器给出的**条件结论**:该带宽对 `w ≤ 13` 足够,而实际 `w` 未测;
> 当前只能据此确定应当监控的量,不能声明带宽已经足够。

**命题 5.3(全量的带前提充分触发)** —— 即改写后的 P3。先显式要求:

1. artifact universe 稳定;
2. `dep` 可靠且稳定,机器的 `dep̂` 持有定理 5.1 覆盖候选态实际读集的跨步上近似证书;
3. judge 与 producer 均 deterministic / hermetic;
4. `P(R)` 的基例证书已建立且仍有效。

在这些前提下,以下两项各自都是全量重验的**充分触发**,但不再声称是必要条件或穷尽枚举:

1. **强化 `P`**(装门或收紧门):基例须重新建立,故全量一次。
2. **改动已声明的全局参数**:即出现在所有 `x` 的 `dep(x)` 中的输入,如 toolchain pin、mathlib rev、
   判者语义或规则目录。

原「恰有两种」已被三种互不相同的第三触发分别证伪:

1. **未声明的环境漂移 / 非 hermetic 判者**——本仓案卷 **#3369 / commit `51a7e128a`**:
   同代码同树,随继承 locale(`LC_ALL=C.UTF-8` 与 `LC_ALL=C`)红绿不同。`P` 未强化、仓内显式全局参数未改,
   归纳步仍失效。
2. **归纳基例 `P(R)` 的证书缺失或失效**——首次启用、发现历史判者不健全、证书不可用,皆属此类。
3. **依赖 / disjointness 证书无法建立**——本仓案卷 **#3274**:deriver 失败、结果非法或
   `incomplete-derivation` 时,即使 `P` 未强化、声明的全局参数未改,也必须回落全量。

若把任一此类变化重命名为「全局参数变更」来保住原命题,P3 就会退化为不可证伪的同义反复。
故这里保留变化的真实类型,不再用改名维护「恰有两种」。显式枚举并最小化全局参数仍能减少
`O(|R|)` 触发器,但它不是全量触发的完备清单。

> **本仓实测(增量回落具备 fail-closed 形,可靠上近似证书仍待核)**:
> `.github/workflows/ci.yml:91` `Decide candidate engineering scope`。唯一跳过全量的理由是 `proven-disjoint`;
> 其余七种情形一律回落全量:dev push、solution root 不可唯一派生、delta 命中工程根、
> 派生进程失败、结果格式非法、`incomplete-derivation`、事件类型不识别。
> 且 `dep` 不是手抄清单:`tools/StrataLint.Engine/RepositoryIo/EngineeringScopePolicy.cs:29 EngineeringInputDeriver`
> 由 MSBuild `Compile` 项与工程判者消费映射现算工程分支,查询不完整时返回 `IncompleteDerivation` 而非猜。
> 该分支**不是** producer 的 `I_prod(x)`,也不单独等于覆盖 `V_path` 等全部判者域的 `ActualReads_R`。
> 完整 `dep̂` 必须并入所有判者域;缺任一域即不得给 `proven-disjoint`。成功派生结果是否同时覆盖
> 两态全域实际读集,仍须由跨步实例证书证明。
> 本模型只指出应把分型后的读取关系升为登记表的一等关系,
> 让 scope 决策对所有门统一,而不是每道门各写一遍。

> **推论(为什么 mathlib pin 升级必然贵)**:pin 是全局参数,故 bump 是 `O(|R|)`,**这是必然,不是工程失误**。
> #1947 的工程错误在于试图把它做成增量——把旧环境的 axiom 闭包存进账本再比对,
> 于是需要重建 v4.31 全仓,即重放一个已死环境的判词。
> 在命题 5.3 的前提成立时,正解是接受一次 `O(|R|)`,且**比对对象是许可集,不是存档旧值**
> (CLAUDE.md 2026-08-16 已独立得出同一结论;本模型给出它的推导)。

---

## §6 判者的两重义务:健全性与活性

用户说「一定程度上似乎测试在做这个事情,但应该还有 CI 门禁」。二者不是两件事,是塔的两个相邻层:

```
τ_max      内容(Lean 声明 / 文档 / 数据)
τ_max−1    单元与集成测试        —— 判内容
τ_max−2    变异证明 / 架构测试    —— 判测试
τ_max−3    CI workflow           —— 判「哪些判者会被执行」
τ_max−4    base 侧 workflow 文本 / required check 集合
…
τ=0        信任根(genesis,judge: open)
```

**每个判者带两个独立义务**:
- **健全性**:它说的是对的(admit 该 admit 的,reject 该 reject 的)。
- **活性**:它**真的会跑**。

**定理 6.1**:测试套件默认只钉健全性;活性必须被单独钉住,而几乎从不被钉。
> **本仓判例(CLAUDE.md 已记,此处只归位)**:给 workflow 的 `Strip checkout remote state` 步骤
> 加一行 `if: false`,四处覆盖 + 11 条契约 + YAML 结构派生的整套机器,**16 个测试全过**——
> 因为它们只校验该步骤**长什么样**,不校验它**会不会执行**。
> 补法是把 `if` 表达式本身纳入契约(11→12)。
> **在本模型里这不是一次疏忽,是一条结构性预测**:凡判者的活性未被单独钉住,该判者可被无声关闭。

**定理 6.2(检测的存在性只能由变异判定)**:「机制在」不蕴含「检测在」。
判据只有一个:打断生产机制,看是否有**具名**测试变红。
> 该判据的完整形是六元组(CLAUDE.md 现役):变异位置 → 具名红测试 → `compile_errors=0` → 退出码 → 还原 →
> **预期红的条数与名字(写在跑之前)**。第六项判的是「该红的都红了没有」,而空钉子恰住在放行侧。

**推论(放行侧天然盲)**:一个「什么都拒绝」的坏门能通过一整套只测拒绝的用例。
凡命题形如「授权齐备时应当接受」,必须单独钉住。

---

## §7 本仓实测对照表(可执行)

按本模型逐条对照 `trureturing@25c3a9716`。**「已满足」栏是正面结论,不是客套**。

| # | 律 | 现状 | 读数 |
|---|---|---|---|
| 0 | 谓词 `Registered` | **已满足** | `FileMapPolicy.cs:520,548` 两向 fail-closed |
| 0 | 谓词 `RefIntegrity`(逐名) | **已满足** | 同文件 #1116 注记;`.Any` 已改逐名 |
| 0 | 粒度律(定理 2.2) | **已满足** | TOWER 16 组件细在 harness;FILEMAP 63 pattern 覆盖 29,469 文件 |
| 0 | 塔顶诚实标 open | **已满足** | `TOWER.yaml` bootstrap `judge: open` |
| 0 | 增量须证明 disjoint | **fail-closed 形已满足;证书义务待核** | `ci.yml:91`,七种回落全量;成功派生的 `dep̂` 仍须证明跨步覆盖候选态实际读集 |
| 1 | 谓词 `ConsumerConform` | **无完整对侧可核** | FILEMAP 无 `I_run`;`consumed_by` 还含不在 `A(R)` 内的仓外 actor |
| 2 | FILEMAP / TOWER 所有权 | **对象域不同,非差距** | `verified_by` 35、`judged_by` 10、交集 1/35;该交集不证明双真源 |
| 3 | TOWER `repository-files` 成员 | **advisory,不作为合并依据** | 10 个组件,38 行成员、31 条去重实路径;全部五种 kind 合计才是 82 行 |
| 4 | GC 消费可达性 | **advisory,未采纳** | 18/63 使用合法 `ProgramActorWords`;当前值为非缺陷 |
| 5 | 投影四项分类 + 规范性裁决 | **由 CLAUDE.md 第〇节直接授权,不是本文定理** | 成本读数是裁决理由;重算只验第三项且不设门;producer 语义另判 |
| 6 | 准入签名 `H : base → δ → Verdict` | **未满足** | `ci.yml:749` 候选自带判官;由 rc=3 脚手架承担,CLAUDE.md 自记为 bootstrap |

**撤回原先的「最高价值项」及合并处方。** 两表的天然对象域和消费者不同:

- FILEMAP 承载 `V_path ⊆ Selector × VerifierActor`,负责全 tracked-tree 的 selector 双射与文件职责。
- TOWER 承载 `J_component ⊆ Component × Component`,负责组件判定边、闭合、无环并终于 bootstrap;
  成员空间有五种:`repository-files` / `rule-catalog` / `ci-jobs` / `path-prefixes` / `artifact-classes`,
  消费者为 `CoverageCommand`、`TowerActualValidator`、`SelfTestGovernancePolicy`。

`verified_by` 35 个名字与 `judged_by` 10 个名字的词表交集为 1(`architecture-tests`),即 1/35。
这恰好证明**域不同**,不证明「同一事实双写」。FILEMAP 没有组件成员语义,不能派生 TOWER 的
rule-catalog / ci-jobs / bootstrap 信任链;TOWER 也不能替代 FILEMAP 的全树 selector 双射。
把二者合并是越权,不是把事实收归天然 owner。

卷宗 `docs/develop/spec/golden-ledger-repo-spec.md` 的 `v7.14 R10`(2026-08-09)已经记载:
六席哲学面板一致否决「成员规则 + 派生 digest」,因为实测该形态使合并**更差**
(36 行地址块三方合并 0 冲突 → 单 digest 1 冲突);它优化的「成员集合单独变化」在 TOWER 全史
94 次改动中发生 **0 次**。该轮净 −924 行,25 分钟仪式已离开每-PR 关键路径。

**程序错误自述**:本模型是在**未翻卷宗**的情况下提出该建议,违反 CLAUDE.md 第 12 条
「先翻卷宗后立新案」。因此本轮撤回建议,不以新变体替换它。

**另案 advisory,不进本轮计划**:parsimony 席提出变体 C′——把不可再约的治理事实收进既有登记表,
为当前消费者派生视图,删除 TOWER 的 tracked 表示与专属守卫。该席给出的**毛上限 1174 行**为
`tools/TOWER.yaml` 191 + `TowerManifestParser.cs` 130 + `TowerActualValidator.cs` 321 +
`TowerManifest.cs` 288 + `TowerManifestTests.cs` 244,净估 −200~−500;但该席自标
`ASSUMED-UNVERIFIED`。按 `DecisionGrounding`,它未点名当前损害案底,故只可另案评估,不进本轮。

**TOWER 读数勘正**:`repository-files` 的 10 个组件共有 38 行成员、31 条去重实路径;
82 是全部五种 kind 的 member 行总数。原读数 28 的错因是提取时用 `grep '/'` 过滤,
静默丢掉三个仓根成员 `Directory.Build.props`、`Directory.Packages.props`、`global.json`;
故 `28 + 3 = 31`。

---

## §8 本仓已验的实例化形状

以下七步只概括 `trureturing@25c3a9716` 上已经核过的结构,不冒领跨仓样本:

1. **枚举与登记**:建立 `Reg`,与 tracked 树在 selector 粒度双射,两向 fail-closed。新文件**未分类即拒**。
2. **分轴**:每条目定 (权威, 居所)。无法判定者在**唯一登记真源**内 fail-closed:
   判为非投影、拒绝准入并记具名 `open`;四项合取成立者按 CLAUDE.md 第〇节规范性裁决不设投影门;
   该裁决所列成本读数只作理由,不得另立平行隔离清单。
3. **补判者**:每个 `source` 必须按两端对象域点名 `J_{D,K}(x)`。无判者的 source 三选一——加判者、降为 projection、删。
4. **核消费者域**:每条目点名 `C(x)`;工件引用与合法 `ProgramActorWords` 按各自对象域解析。
   只有另案采纳 GC 可达性时,才需要进一步区分 `deliverable` 与死工件。
5. **算 τ**:仅由 `J_component` 求高度;查组件判定边无环(谓词 `WellGoverned`);查判者在 base 侧解析(准入签名)。
   `V_path` 不参与 τ,且 τ 永不手写。
6. **审门**:每个门查两态局部性,且 `dep̂` 必须持有覆盖
   全部判者域(含 `V_path`)之 `ActualReads_R ∪ ActualReads_{R⊕δ}` 的跨步可靠上近似证书。
   非局部者可采用定理 5.2 所列三种可靠修法之一、全量重验或另经证明的可靠处置;
   容差带按 `(w−1)·k` 定尺寸,`w` 要实测。
7. **枚举全局参数与环境闭包**:写成显式清单并保持最小;参数变更是充分触发之一,
   证书缺失、派生失败或未声明环境漂移同样会使全量成为必要回落。

**次序不可交换**(CLAUDE.md 2026-08-16 判例):系统仍在合入时,**先立门(只作用于新增项),再补存量**。
反序则在补录与立门之间的窗口继续漏进新的不满足者,补录追的是移动靶。
且立门必须对存量盲,否则立门当场把全仓判红,反而逼人先补,又绕回反序。

**跨仓推广的条件命题**:对满足以下前提的仓库——有限 tracked tree、闭世界工件枚举、
hermetic 且 deterministic 的 judge 与 producer、可证明的依赖上近似——上述形状可作为实例化候选。
该条件命题**尚未在第二个仓库上验证**,保持 `open`,不得改写成「任一 git 仓库」的无条件结论。

---

## §9 健康度指标(全部可测)

| 指标 | 目标 | 本仓当前 |
|---|---|---|
| 未登记文件数 | 0 | **0**(机器保证) |
| 无判者的 source 数 | 0 | 未测 |
| 施于投影的准入门数 | 0(四项分类 + CLAUDE.md 第〇节规范性裁决;成本读数仅为裁决理由) | 未测 |
| 消费者非工件的条目占比 | 仅当采纳 GC 可达性时适用 | **29%**(18/63,非缺陷) |
| FILEMAP / TOWER 词表交集 | 不作为双真源判据 | **1/35**(对象域不同,非缺陷) |
| 手工枚举的成员路径数 | 仅另案采纳派生表示时适用 | **31**(TOWER `repository-files`,38 行) |
| 非局部门的数量 | 显式枚举且有限 | 未测(已知 ≥1:目录容量) |
| 全局参数数量 | 显式枚举且最小 | 未测(已知含 `lean-toolchain`、mathlib rev、规则目录) |
| 每 PR 门代价 | `O(|δ|)` | 部分(.NET 面会发射 `proven-disjoint`,其跨步上近似证书未测;Lean 面走缓存) |
| 判者活性被钉住的比例 | 100% | 未测(已知曾为 0,见 `if: false` 判例) |

---

## §10 未测与 open

诚实分栏。以下为本轮**没有测**的,及其测法:

- **(a) 准入签名缺口的实际可利用性**`open`。本轮只读了 `ci.yml` 的步骤名与 CLAUDE.md 的记载,
  **未构造**「候选提交一个恒 admit 的判者」的实验。测法:在集成分支上把判者的 admit 路径变异为恒真,
  看三条 required check 是否仍全绿。**在做这个实验之前,不得声称本仓可被此路径攻破**——
  当前只能说「准入实现在文本上与该签名不符」。
- **(b) 无判者的 source 数量**`open`。需要先按修正后的投影前提分类 source,再从各定型关系 `J_{D,K}` 计算;
  本轮未作该全量分类。
- **(c) 合并并发宽度 `w`**`open`。定理 5.2 的容差带尺寸依赖它。
  测法:取最近 N 个合入 dev 的 PR,统计「同时处于开启且 base 相同」的最大集合基数。
  当前带宽 12 对 `w ≤ 13` 可靠;`w` 未测,故**不得声称当前带宽足够**,只能说它给出了明确的监控量。
- **(d) 本模型自身没有判者**。本文件是 `kind=data`,`verified_by=SnapshotDecoder`,即只验它能被解码,不验它说得对。
  按定理 6.1,它现在处在「健全性未钉、活性未钉」的状态。**这是提案的正当状态,不是缺陷**;
  它要成为律法,须走 §8 第 3 步:按两端对象域点名 `J_{D,K}(自己)`——即把 §9 的指标做成机器可算的巡检。
- **(e) 跨仓条件命题是否可推广**`open`。P1 的实现结论只覆盖 `trureturing@25c3a9716` 的
  63 条 pattern。对有限 tracked tree、闭世界工件枚举、hermetic/deterministic judge 与 producer、
  可证明依赖上近似的仓库,§8 的形状是否仍成立,尚未在第二个仓库验证。
- **(f) 跨步依赖证书**`open`。本轮核到失败时回落全量的 fail-closed 形,未证明成功派生的 `dep̂`
  同时覆盖两态的全部判者域(含 `V_path`);在此证书建立前,不得由局部域或基线读集单独授权增量跳过。
- **(g) 投影门的信息陈述**`open`:是否存在一个**非空洞**的形式陈述,使「施于投影的门不增加信息」成立?
  v0.1 的失败是**循环**:把「`x` 不承担独立治理权威」同时放进前提与结论。v0.2 的失败是**空洞**:
  deterministic `f` 与 `x=f(I)` 已同义给出原结论,其余前提不起作用;且原装置把 `H` 条件于 `f`,`f` 可硬编码闭包 `I` 外常量。
  任何新尝试必须先说明如何**同时**避开这两种失败模式,否则不必开始。

- **(h) 「不设投影门」的依据形状**已按政策归位。
  三席各自独立指出:四项合取只回答「什么**是**投影」;所引成本读数只证明**三种特定拓扑**很贵
  (保护面误圈计算物 529s/次、`c0` 仪式约 24 min/次、tracked projection 冲突补偿长出
  2,817 行 shell + 3,913 行测试且约 396s)。**二者都不蕴含「所有投影的准入门数应为 0」这条全称规则**
  ——它们没有比较任意投影门的判定收益,也没有给出门数为 0 的推导。
  且 `CLAUDE.md` 第〇节把「不设投影门」写成**规范性第一性原则**,其依据是**权威方向**与
  `projection = f(source)`,而把上述数字放在**「反面即病 / 症状」**名下。
  旧稿把症状改称依据,**与唯一真源的论证形状不一致**。本轮已修为:§3 改动规则表的
  `projection → 无门` 一行只由
  `CLAUDE.md` 的**规范性裁决**直接授权,并把成本读数如实标为**该裁决的理由**而非本文的推导;
  §7 / §8 / §9 / 附录中的标签已同步归位。本文仍不声称从这些理由推出该全称政策。

- **(i) `π` 分型的半传播**已修。
  §1 已把 `π` 定型为 `A(R) → ProducerActor` 并引入部分解析 `resolve_R : ProducerActor ⇀ A(R)`,
  旧稿 §2 把 `π(x)` 直接放在同域工件边上,§3 亦以「某节点因是某个 `π(y)` 而成为 producer」表述,
  在新定义下**不良类型**。本轮凡需要工件节点处均改写为 `resolve_R(π(x))`,并规定未解析、非唯一解析或
  域外解析时关系保持未定义且 fail-closed;未解析 producer 不产生 artifact 边,也不得被当作空边省略。

---

## v0.2 勘误记录

- E1 `I` 同时充当生产与消费读取且与 `C` 互逆 → 撤销 → 依据:fidelity 席 + `Meta/FILEMAP.toml:407-411` / `FileMapPolicy.cs:81-87`。
- E2 施于投影的门不可能产真阳性 → 弱化 → 依据:parsimony 席 + 本文 §10-g 的 producer 可硬编码闭包外常量失败模式。
- E3 「登记表可算的 dep」足以支撑增量可靠性 → 弱化 → 依据:teleology / natural-ownership / proportional-containment 席 + 案卷 `#3274` / `.github/workflows/ci.yml:91,167-175` 的分歧与 fail-closed 回落。
- E4 全量重验触发「恰有两种」且为充要条件 → 撤销 → 依据:teleology / natural-ownership / proportional-containment 席 + 案卷 `#3369` / commit `51a7e128a` 与案卷 `#3274`。
- E5 模型与七步无条件适用于任一 git 仓库 → 弱化 → 依据:proportional-containment 席 + 本文 §8 与 §10-e 的单仓样本边界。
- E6 FILEMAP 与 TOWER 是同一 `J` 的两个真源,TOWER 应合并为 FILEMAP 投影 → 撤销 → 依据:natural-ownership 席 + `docs/develop/spec/golden-ledger-repo-spec.md` 的 `v7.14 R10`。
- E7 消费者非工件的 18/63 即 29% 缺陷 → 撤销 → 依据:caller + fidelity / natural-ownership / teleology 席 + `FileMapPolicy.cs:81-87` / `Meta/FILEMAP.toml:407-411`。
- E8 TOWER 为 82 行 `repository-files` 成员、28 路径,且 29,407 属当前基线 → 勘正 → 依据:caller 原读数 + fidelity 席复算 + `tools/TOWER.yaml:108-116` / commits `25c3a9716`,`94f64f416`。
- E9 产地未按第 9′ 条披露 → 勘正 → 依据:orchestrator + `CLAUDE.md` 第 9′ 条;`/consensus-rnd:sshx` 六席 = 5× codex-cli(teleology / parsimony / fidelity / natural-ownership / proportional-containment)+1× nyxid-oracle(worth),`reject 2 / revise 4`;worth attempt 1 `extraction_failure` abstained、attempt 2 完成;五席同载体族,不声称模型多样性;读数均由 orchestrator 亲验或复核。
- E10 定理 5.2 目录容差带结论 → 弱化 → 依据:v0.1 使用了 `CLAUDE.md` 第Ⅵ节禁止的模糊措辞「很可能」;`w` 未测,故不得声称当前带宽足够。
- E11 定理 3.1 → 降格为政策 + open 问题 → 依据:第 2 轮三席一致判其换结论空洞;两次失败模式(循环 / 同义反复且 `H` 条件于 `f`)已记入 open 条目。
- E12 `π(x)` 可直接作为工件端点进入 `Π_D`,未解析 producer 可由省略边处理 → 改为仅由 `resolve_R(π(x))` 产生工件边,未解析关系未定义且 fail-closed → 依据:FocusedRound architecture / fidelity 席的分型检查;`ProducerActor` 与 `A(R)` 是不同对象域。
- E13 「投影不设门」由本文成本读数推出 → 归位为 CLAUDE.md 第〇节规范性裁决直接授权,成本读数仅作该裁决的理由 → 依据:FocusedRound 六席一致结论 + CLAUDE.md 第〇节唯一真源。
- E14 `J` 中有环使 `H=F(H)` 有多个不动点且恒含全部 admit → 撤销并给出一节点环配常拒绝 `F` 的反例 → 依据:fidelity 席反例;该例只有全部 reject 一个不动点。
- E15 非局部谓词的可靠修法恰有三种 → 弱化为所列三种均可靠、但不穷尽 → 依据:fidelity 席反例;全量重验本身即第四种可靠处置。
- E16 本模型零公理且承重句子穷尽于定义/谓词/定理三类 → 改为六类诚实分栏 → 依据:fidelity 席分类;外部 git 契约、规范性政策、经验/设计选择与实例测量义务均不属于原三类。

---

## 附:与既有文本的关系

本模型不新增任何律。它做三件事:
① 把 CLAUDE.md 中散布的条款归约到分型的生产、运行时消费与判定关系,并明确各定理或政策的依据
(增量可靠性 ← 定理 5.1 的跨步上近似证书;投影分类 ← 四项合取、不设投影门 ← CLAUDE.md 第〇节规范性裁决,
成本读数仅为该裁决的理由;
变异证明 ← 定理 6.1/6.2;
全量充分触发 ← 命题 5.3);
② 区分 FILEMAP 与 TOWER 的对象域,并保留 §4 谓词 `RefIntegrity` 的逐名量词检查,不再用词表交集诊断双真源;
③ 给出本仓已验的七步形状;跨仓推广只对满足 §8 前提的仓库成立为待验证条件命题。

凡本文件与 spec / CLAUDE.md 冲突,以后二者为准;凡本文件的读数与实测冲突,以实测为准并勘正本文件。
