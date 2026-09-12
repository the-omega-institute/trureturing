## 第 20 轮靶已闭合;下一轮**无机器可选之靶**(2026-09-12)

`commutant_isSemisimpleRing_of_unitary` 已冻结并合入 dev(PR 7098,
`D5/S3/Quantum/Matrix/CommutantSemisimple`,`generality: G`,
`statement_id sha256:50a83d557929`)。同模块一并冻结:

- `jacobson_eq_bot_of_conjTranspose_closed` —— 预登记的具名见证,`proof_shape: content`,
  `admission_basis: escape-witness`;
- `unitary_commutant_has_record_capacity` —— **消费者**:把 `RecordCapacity` 那条的
  `[IsSemisimpleRing (commutant U)]` 实例假设换成 `∀ g, U g ∈ unitary`,证明体即
  `commutant_isSemisimpleRing_of_unitary U hU` 接原定理;
- `not_all_integer_matrix_commutants_semisimple` —— 反例,经 SL-031 的**有界形式反驳硬门**
  (`claim` / `result` 类型与 `Not claim` 定义相等且经类型推断相符),证明酉性是承重假设而非装饰。

orchestrator 独立复核:`sorry` 0、自定义 `axiom` 0、G 只 import G(`RecordCapacity`,SL-010)、
三门绿、冻结片在 dev 上。**判词提出的路线(⋆-闭包而非 Maschke)由编译确认成立。**

### 下一轮的状态:无靶,暂停派席

`TERRAIN-MAP.md` 第三节现在**四项全部标 `物理输入`** —— 原先唯一标「数学,可做」的那一项
就是本轮闭合的这个。按 第 3.6 条,**机器不替人选第三档目标**,采纳哪条物理输入由 τ=0 点题。

**这是合法终态,不是没找到题。** 逐项的挡因:

| 剩余缺口 | 为什么机器不能自选 |
|---|---|
| objectivity 本身 | 需要「记录/环境分片结构为何出现」这条物理输入,观察者假设不给 |
| cross-species 共享 active symmetry | 同上,见第 14 轮定价表 |
| §17.1 / §18 量子统计层 | canonical quantization;`ρ_C ⊗ ρ_β` 是新制备条件 |
| Einstein 方程 | Fierz–Pauli / spin-2 本身即新输入,非观察者假设的后果 |

**下一轮若无 τ=0 点题,记「本轮无靶,暂停派席」,不为了有产出而把物理输入当数学题派。**
另:**不得再以 `pool` 参数绕过 `BAD_SCRIPTS`**(见本单同日的载体更正)。

### 本线当前的瓶颈是冻结,不是选题(dev `1dc1faa837` 读数)

复查 `e79baa101c → 1dc1faa837` 的 44 个提交:量子面**新增 5 个模块、新增冻结状态片 0 个**,
五个都是 `Tomography/MUB/`(复 Hadamard / 相对 Gram cocycle / 双补全 / 亲和度阈值),
与第三节四项物理输入**一项不沾**,故地形未动。

但同一次普查给出更要紧的一组数:

```
Quantum 模块 253    已冻结 240    未冻结 13(全部在 Tomography/MUB/)
```

按 第 1.3 条,只有冻结才进真值 DAG;未冻结模块对本线地形图零贡献——
既进不了 `TERRAIN-MAP` 第一节,也当不了下一层的前置。
**故本线下一步的正解不是找靶,是把已写好的冻掉**:
其中 11 个(`utility: none`,不缺头)已在一条批量补冻 lane 内;
`ComplexHadamardCocycleGauge` 与 `MUBCompletionRelativeGramEquivalence` 是该 lane 切出后才落 dev 的,须补一轮。
补冻合入前,「11 个将被冻结」是计划不是事实,不得计入。

---

## 本轮:**`RecordCapacity` 的半单性假设能不能卸掉,以及该走哪条路**(第 20 轮)

仓库 https://github.com/the-omega-institute/trureturing
本轮全部仓内引用钉在 `852514a48bb4793f9d29270993610c84bf671559`,请按该提交读,不要读 dev tip。

### 为什么是这个靶(而不是又一轮表态)

`TERRAIN-MAP.md` 第三节列五个缺口,**四个标 `物理输入`**(objectivity 本身 /
cross-species 共享 active symmetry / §17.1–18 量子统计层 / Einstein 方程)。
按第 3.6 条,机器不替人选第三档目标,那四项等 τ=0 点题。
**只剩一个标「数学,可做」**,就是本轮的靶。

第 19 轮的「该停」只针对**表态类的整类重裁**,本轮不是表态轮。

### 靶的精确形状(orchestrator 亲验,行号可复核)

`D5/S3/Quantum/Matrix/RecordCapacity.lean`,**已冻结**,`generality: G`:

```
139: theorem semisimple_commutant_has_record_capacity
140:     {G n : Type*} [Group G] [Fintype n] [DecidableEq n]
141:     (U : G →* Matrix n n ℂ) [IsSemisimpleRing (commutant U)] :
142:     ∃ (k : ℕ) (m : Fin k → ℕ), (∀ b, NeZero (m b)) ∧
143:       Nonempty (commutant U ≃ₐ[ℂ] ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) ∧ …
```

其证明一步用 `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (commutant U)`。
`commutant U`(第 57 行)是 `U` 的实际交换子代数。

**注意地形图的措辞与这段源码不一致,这正是 Q1 的由来**:地形图写「半单性由酉性导出(Maschke)」,
而该定理里 **`G` 是任意群**(`[Group G]`,无有限性、无紧性、无拓扑),
**`U` 只是到矩阵的幺半群同态,酉性根本不在假设里**。

### Q1(主问):这条假设卸得掉吗,代价是什么

逐项回答,每项给可复核出处(钉版 mathlib 的声明名与文件,或文献的定理编号):

1. 若**追加**「∀ g, `U g ∈ unitary (Matrix n n ℂ)`」,`IsSemisimpleRing (commutant U)` 是否随之成立?
2. 两条候选路径哪条对、各要什么前提:
   **(i) Maschke** —— 需要 `G` 有限或紧(以及特征零/可积分),那对任意群不成立;
   **(ii) \*-闭包** —— `U g` 酉 ⟹ `A ∈ commutant ⟹ A* ∈ commutant`(因 `g ↦ g⁻¹` 是 `G` 的双射),
   故 `commutant U` 是 `M_n(ℂ)` 的有限维 \*-子代数,而有限维 C\*-代数半单。
   **这条对任意群成立,不需要任何有限性** —— 请判断它对不对,若对,地形图第三节的「Maschke」是写错了路。
3. 钉版 mathlib 给到哪一步:有没有「\*-子代数 / 有限维 C\*-代数 ⟹ `IsSemisimpleRing`」的现成声明或实例?
   点名声明与文件路径。若只有零散零件,列出最短组合链。
4. **有没有真障碍**使这条假设是承重的而非可卸的?例如:不假设酉性时 `commutant U` 可以不半单的**具体反例**
   (给出 `G`、`U`、以及交换子代数的显式形状)。**有反例就直接给**,那比「可以卸掉」更有价值。
5. 若卸掉假设需要**加**酉性,那是把一条假设换成另一条 —— 请明说净收益是什么
   (例如:酉性是物理上本来就有的,而半单性是代数技术条件),或者明说「这只是换了个说法,不值得做」。

### Q2(次问,有界):三条从未被裁的来源标签

第 16 轮明确「留作下一轮的具名开项」:`RecordCapacity` 的
`card_le_finrank_of_idempotent_sum`、`algebra_card_le_finrank`、
`equivariant_record_card_le_commutant_finrank` 三条仍标 `FromRepo`,**从未被裁过**。
逐条判 **(a)** 标准结果 / **(b)** 确属本仓推导 / **(c)** 判不了,(a) 须给可复核来源链。
**(c) 是合法答案。** 这是首次裁,不是第 19 轮所禁的重裁。

### Q3:这次应当在哪里停

若 Q1 的结论是「卸不掉」或「卸掉不值得」,**照直说**,不要为了给出行动项而拼一条路线。

### 不在本轮范围

四项 `物理输入` 缺口;表态类的整类重裁;任何需要跑 Lean / 构建 / 渲染的断言
(你没有文件系统,凡涉及「跑过什么」一律标 `ASSUMED-UNVERIFIED`)。


### 结算(第 20 轮判词已收,2026-09-12)

**载体**:`nyx.sh` 遍历的三个池全部终局失败(`infrastructure_retry_exhausted` ×2、
`composer_draft_conflict` ×1;三个 task id 均已提交,逐个 `result` 取回确认不是可取答案
——与第 19 轮的 TIMEOUT 不同,那次任务仍在飞故可取,**两者不是同一症状**)。
`nyxid oracle pool list` 显示**五个池全 active,而 `nyx.sh` 只遍历三个**;
钉住从未试过的 `chatgpt-pro-pool` 重派,`NYX_OK` 一次成功。鉴权正常,非 τ=0 能力缺口。

**Q1 结论**:假设**不能直接删**;**追加酉性后可卸,且对任意群成立**,不需有限或紧。
路线是 **⋆-闭包 → Jacobson 根基为零 → 半单**,**不是 Maschke**;地形图第三节该行已据此更正。
不加酉性的反例(orchestrator 手算复核):`G = ℤ`、`U n = [[1,n],[0,1]]`,
交换子 `≅ ℂ[ε]/(ε²)`,根基 `(ε) ≠ 0`,不半单 —— 故 `hU` 是承重假设。

**Q2 撤回,前提不成立**:我在题面里照抄第 16 轮的「三条仍标 `FromRepo`」而未核当前树;
席位反过来更正我且它是对的 —— `RecordCapacity.scribe.cs` @ `852514a48b` 的三处
(第 28 / 32 / 36 行)**各自显式传 `true`**,走 `FromLiterature` 分支。
第 16 轮那条具名开项就此关闭(理由是已解决,不是被忽略)。
同文件 7 个调用点全部显式传参,`bool literature = false` 默认值**存在但从未被走到**。

**产出的形式化靶**(已派席 `commutant-ss-1`):

```lean
theorem commutant_isSemisimpleRing_of_unitary
    {G n : Type*} [Group G] [Fintype n] [DecidableEq n]
    (U : G →* Matrix n n ℂ) (hU : ∀ g, U g ∈ unitary (Matrix n n ℂ)) :
    IsSemisimpleRing (commutant U)
```

具名见证 `jacobson_eq_bot_of_conjTranspose_closed`;上游入口
`Artinian/Module.lean:650 isSemisimpleRing_iff_jacobson`、`Algebra/Star/Unitary.lean:116 star_eq_inv`
(两处 orchestrator 已复核存在)。席位自标该签名 `ASSUMED-UNVERIFIED`,未编译过。

**席位自划的未验边界**:未取得 `#6298` 评论正文(公开页只给主帖,两个评论 API 入口均失败),
故不把内联提供的前轮结算冒充为它读到的评论链;仓内判断钉在 `852514a48b`,
mathlib 钉在 `db584cd6d4`;Scribe 标签只证明当前源码,不证明它们在评论史上何时被裁过。
**orchestrator 未复核**:Jacobson 根基为零那一步的完整代数论证与其钉版支持面。


---

## 本轮:**清零之后又长出十七条 —— 表态类真的闭合了吗**(第 19 轮,2026-09-11)

### 为什么这不是对同一批存量的第四次重问

第 17 轮把地形图所列模块的 29 条 `Repository-derived` 一次性裁完,三段处置已全部合入 dev,
**存量归零**(orchestrator 在 dev 上逐模块复算,合计 0)。我当时在靶里写死了「这是最后一轮表态轮」。

**但同一会话内,新落地的六个模块又产生了 17 条 `Repository-derived`。**
清的是**存量**,再生的机制没有被碰过。按第 7.11 条,同症状以新形态再现,
该问的是「为什么会再生」,不是再扫一遍存量。

### orchestrator 亲跑的读数(本会话新模块,dev 上复算)

| 模块 | `Repository-derived` | `Citation` |
| --- | ---: | ---: |
| `D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount` | **5** | 0 |
| `D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros` | 5 | 1 |
| `D5/S3/Analytic/Entire/SquareShadowOrderHalving` | 3 | 4 |
| `D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity` | 3 | 1 |
| `D5/S1/Words/AdmissibleWords/PathStableSetPolytope` | 1 | 1 |
| `D5/S3/Analytic/HolonomyDeterminant/ReflectedHurwitzDerivative` | **0** | 1 |

**末行值得注意**:那个模块证的是 **Lerch 公式**(经典具名结果),席位**自己**标了文献来源。
同一批席位里有人标对了 —— 所以这不是「席位不会标」,是**没有任何东西要求它标**。

### Q1:这 17 条各自是什么

逐条判 **(a)** 标准结果 / **(b)** 确属本仓推导 / **(c)** 判不了,
口径沿用第 16、17 轮(「文献明确陈述**或可逐步核对的标准直接推论**」),(a) 须给可复核来源链。
**(c) 是合法答案**,比硬塞一个来源好。十七条的逐条身份:

- `StepGraphComponentCount`(5):区间图的定义、出现余数的定义、
  「可达 ⟺ 余数相等」、分量与出现余数的对应、分量数 = `min(m,d)`
- `FiniteDivisorPartitionZeros`(5):有限几何因子的定义、有限因数配分函数的定义、
  「局部零点实部为零」、「远离虚轴不为零」、「每个零点都在虚轴上」
- `SquareShadowOrderHalving`(3):圆周最大模的定义、半径零、最大值取得
- `EnergyEigenstateStationarity`(3):指数在本征向量上的作用、归一化纯密度态的定义、零能量方差
- `PathStableSetPolytope`(1):三坐标四棱锥

**我不预判其中哪些是 (a)。** 本会话已立并合入 dev 的规则是:
**编排者供读数,判断归有能力查证的一方** —— 那条规则是在我三次把缺席结论写错之后立的。

### Q2:再生机制,以及有没有成本相称的办法

第 17 轮的判词已点过一次:`FromRepo` 是**写作时断言**的,
仓内没有任何 fail-closed 消费者会因为「这条从没被裁过」而变红;
若干模块的 Scribe 助手还把 `literature` 做成**默认 false 的可选参数**,
于是表态可由**遗漏**产生。第 3.4 条 把这一条记作 `open`(#5515),并明说**不为它新建机器门**。

**问**:在不新建机器门的前提下,有没有**成本相称**的办法,
使「新模块的表态是被考虑过的」可审计?可考虑的方向(不限于此):
把逐声明表态与理由列为交付的必填项(由评审读,不由机器判);
或去掉那个默认参数,强制每处显式写 `FromRepo` 或 `FromLiterature(...)`。

**若你判断「没有比现状更好的低成本办法」,照直说** —— 那也是一个可用的结论,
它会让我停止在这上面投入(第 2.7 条 预算包络)。

### 不在本轮范围

物理前沿四项仍卡在 τ=0 的物理输入上(第 14 轮定价表结论至今未变);
第 3.6 条:机器不替人选第三档目标。**本轮不问那四项。**

---


### 结算(第 19 轮判词已收,2026-09-12)

判词经 `nyxid oracle result` 取回;轮次脚本打的 `status=failed` 是错哨兵,超时不等于失败。

**Q1:(a) 17 / (b) 0 / (c) 0。** 席位对每条给了可复核来源链,并自限 (a) 的含义为
「标准定义的本地表示、文献明确陈述,或可逐步核对的标准直接推论」,**不主张文献逐字印着这些 GID**。

**Q2:有成本相称的办法,且不是新建机器门。** 逐声明一行依据(GID 与版本 / 来源判断 /
可复核出处 / 匹配理由与边界),同源链可复用;**并把来源改成由调用者逐条显式传入**,
取消助手代判。由现有评审读增量,不设常设审查席。

**orchestrator 亲验后的更正**:`StepGraphComponentCount` 的五条来源由 scribe 内
`Entry` helper 硬编码(第 62 行 `AssessedProvenance.FromRepo()`,五个调用点均不传参),
席位的指控成立。而这一类**不含 `literature = false` 这个 token**,故先前按该 token 量得的
「残余 0」判据用错。换判据后的全库读数:**1196 个 scribe 文件**的单个
`DeclarationHandle.Create` 藏在 helper 内、对应 Lean 模块有 >1 条公开声明;
这些模块公开声明合计 **8600**(上界,并非每条都被描述),来源字面量合计 **1769**。

**本靶就此结算,不再以计数为触发器重开**:席位明确不建议宣告「表态这一类永久了结」,
正确的三分是——本批已裁;默认代判的入口已定位;今后正确与否不由该调整保证,
**只有出现具名的依据缺口才重新开题**。机械把 8600 处补成 `FromRepo()` 被明确排除
(「只会把隐式默认改成显式默认」)。


## 第 17 轮结算:29 条表态全部归入「标准结果或其直接推论」(2026-09-11)

**产地三项**:无 skill;靶与那份 29 条清单由 orchestrator 亲跑读数得出,三分判词由
**nyxid / ChatGPT Pro 席**给出(单席);零 codex 席、零评审席。仓内读数 orchestrator 复算,
文献读数逐条标了核到哪一步。完整结算见 issue #6298 的对应评论。

**三分结果:(a) 29 / (b) 0 / (c) 0**,口径是「文献明确陈述**或可逐步核对的标准直接推论**」——
不表示文献里印着同一个 GID,也不表示 Lean 实现没有工作量;**改的是数学陈述的来源登记,
不是实现代码的作者归属**。

### 它纠正了我两处(均已复算确认)

1. `CovarianceSumBound` 的 Cauchy–Schwarz(定理 1.8)与半宽方差界(1.9)**已带 `*Citation.*`**,
   不在待裁之列。我在靶里写「这两条几乎必然是 (a)」是**错的**。实际九条是
   **3 个定义 + 4 条基本性质 + 2 条求和界**。
2. 它严格按固定提交审计,**没有把我在飞的更正倒写进快照**。

### 来源链(席位给出,页码我未亲验)

- **R1** Axler《Linear Algebra Done Right》4ed:§8D 迹的线性性;习题「`P²=P ⟹ tr P = dim range P`」,
  **不限于正交投影**。
- **R2** Etingof 等《Introduction to representation theory》:左正则表示;有限维半单代数 ↔ 矩阵代数有限直和。
- **C1** Gibilisco–Hiai–Petz,arXiv:0712.1208:对称协方差公式。
- **C2** Petz,arXiv:quant-ph/0106125 §2 式 (16):对称双线性形式。
- **C3** Axler 同书 §6A:Cauchy–Schwarz。
- **C4** Sharma–Gupta–Kapoor,*J. Math. Inequal.* **4**(3) 355–363 (2010):Popoviciu 界。

席位把 Popoviciu 标成**实际核到的 2010 年论文**,并明说没有把检索到的 1935 年原始文献
冒充成已逐页核对 —— 这是本轮质量最高的一处自律。

### 处置分三段,不一次吞

| 段 | 范围 | 状态 |
| --- | --- | --- |
| 1 | `RecordCapacity` 六条 | **已合入**(渲染 `Repository-derived` 6 → **0**,`*Citation.*` 7) |
| 2 | `CovarianceSumBound` 九条 | **待做**,需新建 C1/C2/C3/C4 四条 L note |
| 3 | 其余七模块十四条 | **待做**:`CoherentCopyCorrelationTax` 5、`DualAccountFull` 2、`GibbsVariationalIdentity` 2、`FubiniStudyRecordTime` 2、`SpectralReadoutEntropyEquality` 1、`CorrelatedGibbsEnergyIdentity` 1、`PartialTraceMutualInformation` 1 |

`29 = 6 + 9 + 14`,逐模块渲染读数复算一致。
**只改显示标签而不给可复核来源链,是第 16 轮判词明确反对的做法**,故分段做、每段配 note。

---

## 本轮:**无靶,暂停派席**(第 18 轮位次,2026-09-11)

第 5⁵ 条:席位空闲不是派题的理由。逐条说明为什么当前没有该派的问题。

**① 表态这一类已在第 17 轮一次性了结。** 那一轮的靶里就写死了「这是最后一轮表态轮」,
它交回了 29 条的三分与来源链。**剩下的阶段 2、3 是实施,不是提问** ——
来源链已经在手,再派一轮是重问已结之案(第 10.3 条 一事不再理)。

**② 物理前沿四项仍卡在 τ=0 的物理输入上。** observer→objective 桥、cross-species 原理、
§17.1/§18 量子统计层、Einstein 方程 —— 第 14 轮定价表的结论至今未变,四项中三项缺的是
**物理输入而非形式化能力**。第 3.6 条:**机器不替人选第三档目标**。这一项要 τ=0 点题。

**③ 本会话唯一的新发现,oracle 核不了。** 素数线这一轮实测:`quantum-reality` 语料的
定理级 atom **多被上游 mathlib 闭合** —— 定理 178.1 连派两轮、外加一座桥,三个席位全部
证出了东西又全部判自己 bind-only;随后按「搜动作而非复合名」的新纪律筛 定理 358.1 与 268.1,
两分钟内双双挡住(`adjMatrix_pow_apply_eq_card_walk` + `edist_eq_sInf`;`convexHull_prod` +
`convexHull_basis_eq_stdSimplex`)。**这是对本仓语料的测量,oracle 没有本仓可测**,
不构成它能独答的问题。

**复原条件**:出现下列任一即可开第 18 轮 ——
τ=0 就四项右栏中的某一条给出物理输入或指定优先级;
或阶段 2/3 实施中出现**来源链不足以支撑分类**的具体声明(那才是文献问题);
或本线出现新的、需要外部文献判断的断言。

---

## 第 16 轮结算:计数界是**经典结果的标准推论**,表态与地图措辞均已更正(2026-09-11)

**产地三项**:无 skill;靶由 orchestrator 写、问题由 **nyxid / ChatGPT Pro 席**回答;
零 codex 席。下列每条**仓内**读数由 orchestrator 在本机亲验复算,
每条**文献**读数是席位自报、并注明我核到哪一步为止。

### 载体:第一次真正跑完三个池

此前报的「载体不可用」,真因是派发器 `quantum-reality-round.sh` 直接调 `nyxid oracle ask`、
绕过本仓自己的 `nyx.sh`,于是没有 `mode:chat` 标签、没有池遍历、没有判词分类、
没有 task-id 边车(已修,PR 6993)。改走 `nyx.sh` 后本轮实测三池依次为
`INFRA` → `CARRIER` → **`OK`**;**答出本轮的是第三个池,而旧派发器从不曾到达它。**

本文件此前把 `company-chatgpt-pro` 的 `oracle_mode_required` 归因为「runner 不设 mode 标签」:
那对**旧派发器**成立、对 `nyx.sh` 不成立。该归因行已就地更正。

### 判词与我的复算

**问的是**:容量律的计数界(`⊕M_{m_b}` 完全正交幂等族 `≤ Σ m_b`)是不是教科书结果,
以及 `TERRAIN-MAP.md` 里「唯一的定量律」这个措辞站不站得住。

**答:是标准推论,应记 `literature-attested`;措辞应改,但「已知」与「本图内唯一」要分开判。**

推导(可自行复核,不依赖任何页码):令 `A = ∏_b M_{m_b}(ℂ)`,`ℓ_A` 为左 A-模的组成长度。
正则模分解给出 `ℓ_A(A) = Σ_b m_b`;非零幂等族求和为一给出 `A = ⊕_i A p_i`,
每个 `A p_i` 非零(含 `p_i = 1·p_i`)故组成长度 ≥ 1;组成长度对有限直和可加,于是
`|I| ≤ Σ_i ℓ_A(A p_i) = ℓ_A(A) = Σ_b m_b`。
**预算是正则模的组成长度,不是代数维数 `Σ_b m_b²`;两者不得混写。**

**orchestrator 亲验的三条仓内读数(全部命中,不是转述)**:

| 席位的读数 | 我的复算 |
|---|---|
| `RecordCapacity.scribe.cs` 里只有 `sum_range_finrank_of_idempotent_sum` 传 `literature = true`,其余六次走默认 `FromRepo` | ✅ 逐行核对;`Result(...)` 第 7 个参数默认 `false` |
| 渲染正文 Theorem 1.1 有文献引用,1.2–1.7 全部 `Repository-derived` | ✅ `RecordCapacity.md` 逐条核对 |
| `matrix_blocks_card_le_sum` 只要求幂等、非零、求和为一,**不要求两两正交** | ✅ 源码假设位逐条核对 |

**席位自报、我未亲验的部分(如实标注)**:Knapp《Advanced Algebra》与 Etingof 等书内的
**具体页码与定理编号**。我用自己的 fetch 核到了 arXiv 记录 `0901.0827v5`(标题、七位作者、
math.RT)与既有 note 一致;想从该 PDF 确认章节编号时**失败** —— 其文本流用子集字体编码,
本机可用的抽取手段解不开。故 L note 支持的是**数学主张**(计数界是 Artin–Wedderburn 配
Jordan–Hölder 的标准推论,推导已写出),**不是**任何关于「印在哪一页」的主张。

### 处置(已落地)

1. **表态更正**:`matrix_blocks_card_le_sum`、`equivariant_record_card_le_sum`、
   `semisimple_commutant_has_record_capacity` 三条由 `FromRepo` 改为 `FromLiterature`,
   指向扩充后的 `D5/L/Quantum/mathlib2026recordcapacity`。
   **这是漏认前人成果的更正**(第 3.7 条:冒认与漏认同为不诚实)。
2. **L note 扩充**:加入上述组成长度推导、与仓内版本假设更弱的说明,
   以及一节明写本 note attest 什么、不 attest 什么。
3. **地图收窄**:`TERRAIN-MAP.md` 第二节改写,点明两处越界——
   ①计数对象是**等变幂等分解**,不是「客观记录」,它不认定哪些幂等元是记录、也不给 objectivity;
   ②`m_b` 是 **commutant 的 Wedderburn 块尺寸**,不是原表示各不可约分量的重数
   (模块正文本来就写着这条不在形式化范围内)。第一节该行也补齐了记录族的非零/完备/正交/等变条件。
4. **「唯一」保留但加限定**:标题本就带范围限定(本节只收统一多条结构的定量律),
   文献已知不否定栏目内唯一性;但已写明**它不得被当作本线新发现的物理定量律**。

### 本轮不新增研究靶

席位明说:本轮没有新的逃逸见证,也不提出新的首冻候选;计数就是已登记的秩和恒等式,
加上非零像空间维数至少为一,再经忠实作用或代数等价运输。**处置是更正来源登记,
不是为此重新证明同一计数界。**

### 仍开着的一项(不冒领)

`RecordCapacity` 另外三条(`card_le_finrank_of_idempotent_sum`、`algebra_card_le_finrank`、
`equivariant_record_card_le_commutant_finrank`)仍标 `FromRepo`。席位**只裁了直接承载本题的三条**,
没有裁这三条,我也没有独立核过。**不因「看起来也是经典的」就顺手翻**——留作下一轮的具名开项。

---

## 本轮:**同一类风险的第二次自查**(第 16 轮,2026-09-11)

第 15 轮查出 `RecordSymmetryNoGo` 的表态错(`FromRepo` 应为 `FromLiterature`)。
本轮问的是**同一类问题在另一条已合入 dev 的结果上是否也成立**——这不是席位空闲派题,
是一个可点名的风险(第 7.10 条:防的必须是发生过的事;它刚发生过一次)。

### 本轮派发状态:**载体不可用,未能派出**(非「无靶」)

三个池依次失败,判词各不相同,**已按纪律停止换池**(换过两次,第三次即为撞墙):

| 池 | 判词 | 语义 |
|---|---|---|
| `chrono-chatgpt-pro-pool` | `infrastructure_retry_exhausted` | 在 `selecting_model / page_ready` 间空转四次,从未发出 |
| `company-chatgpt-pro` | `oracle_mode_required` | **该归因已过期,见本文件顶部第 16 轮结算**:不设 mode 标签的是旧派发器(它绕过 `nyx.sh` 直调 `nyxid oracle ask`),不是 runner 本身;该池今日以 `tag=mode:chat` 正常接收提交 |
| `chatgpt-pro-pool` | `extraction_failure` | 载体侧随机失败 |

**这不是「本轮无靶」**——Q1 是实靶且有具名风险(见下)。这是 第 5.9 条 的**能力缺口**:
记具名 open、等灯亮,其余 lane 继续推进。**失败归档已删**,不留空壳被下轮误读为判词。

**已知的四种 nyxid 终态,处置各不相同,不可只看 `QR_ROUND status=failed`**:
`extraction_failure`(连两次换池)/ 超时 `still dispatched`(**按 task ID 取,禁重投**)/
`infrastructure_retry_exhausted`(终态,换池)/ `oracle_mode_required`(改调用方式,`retryable: false`)。

**复原条件**:任一池恢复即可按本文件现有 Q1 原样派出,**问题不需重写**。

### Q1:容量律 `card ≤ Σᵢ mᵢ` 的文献状态

已冻结于 `D5/S3/Quantum/Matrix/RecordCapacity`(PR #6962,已合 dev)。其陈述为:

> 设 `U : G →* Matrix n n ℂ`,`commutant U` 半单,由 Wedderburn 取块尺寸 `m`。
> 则任何由非零、两两正交、求和为单位的**等变**幂等组成的族 `P` 满足 `card I ≤ ∑ b, m b`。

该模块内 Wedderburn 那条已表 `FromLiterature`,**但计数那条仍表 `FromRepo`**。

**要回答三件事**:
① 「半单代数 `⊕ M_{mᵢ}` 中,完备正交幂等族的基数 ≤ `Σ mᵢ`」这条计数界,文献里已有吗?给出处。
   (它看起来是 Artin–Wedderburn 之后的标准推论,与「`M_m` 中完备正交幂等族最多 `m` 个」同源。)
② 若已有,本仓该表 `literature-attested` 并建 L note;若确系本仓推导,表 `repo-derived`。
③ **更要紧的一问**:`docs/reports/quantum-reality/TERRAIN-MAP.md` 第二节把它称作
   「**唯一的定量律**」。若①的答案是「已知」,该措辞就是**过度主张**,须改。
   请直接判:这个称呼站得住吗?

**答「已知、该改措辞」是完全可接受的答案。** 第 15 轮已有一次同类更正,
本线不因承认而损失什么——因冒领而损失的更多(第 3.7 条:冒认与漏认同为不诚实)。

### 为什么这一轮值得派席

第 15 轮的教训不是「那一条表错了」,是**表态在写作当时无人核**。
同一形态已出现一次,按 第 7.11 条 该查是否有第二例,而不是等下一次被抓。

### 本线其余状态(不构成本轮问题)

tier-3 四项右栏**已按预算包络停派**:五轮 oracle、四席条件切片,
「四项变成无条件的」计数为 **0**,边际改进触底(第 2.7 条),根因(需 τ=0 给物理输入)在权限外。
语料消化继续:`quantum-reality` 定理 229.1 的 FS 记录时间界已证完待合。

## 第 15 轮结算:no-go 应记为 **`literature-attested`**(2026-09-11)

任务 `333503a8-6b9d-4ad6-9d6e-2c927bfc875b` 已回包(超时后按 ID 取得,未重投)。

### ① 文献状态:**已知**,不得标 `suspected-novel`

判词原文:「**数学陈述已知。**它是 Schur 引理的直接推论;在酉表示的语境下,文献还明确给出了
『不变子空间 ↔ 等变正交投影』的等价表述。**没有依据将这个数学内核标成 suspected-novel**。」

出处:**Etingof 等《Introduction to representation theory》(2011) §1.3, Prop 1.16 / Cor 1.17,
印刷页 8–9**;**Sophie Morel《MAT 449: Representation theory》(2018) §I.3.4,
Thm I.3.4.1 / Lemma I.3.4.3, 印刷页 25–26**(后者直接写出该等价)。
该席同时声明:**未核定最早历史出处**;判 `literature-attested` 不需要先解决首创年代问题。

### ② 与 Zurek / Korbicz 的关系:**不同命题**

- **非 einselection**:Zurek(式 4.21–4.22)的对易对象是**指定的相互作用 Hamiltonian**,
  不是群作用;本 no-go 须额外指定群作用并要求记录投影逐个与之对易,才谈得上表示论限制。
- **非 SBS**:Korbicz 等(*Quantum origins of objectivity*, PRA **91**, 032122, 2015)
  的 SBS 定义(Def 2、式 1–2)**不要求**支撑投影与某个共享不可约群作用对易。

### ③ 该席指出的两处,本线照收

1. **冗余假设**:代数意义的不可约性下,零/一结论**不依赖酉性、自伴性、复数域或有限维性**;
   去掉多余假设**不会**使它成为新结果。⟹ `RecordSymmetryNoGo` 的假设可收紧,且收紧不增新颖性。
2. **互信息平台 ≠ objectivity**:Le 与 Olaya-Castro(2019)区分互信息平台 / strong quantum
   Darwinism / SBS。⟹ **`TERRAIN-MAP.md` 中该行已由「全部经典信息 / objectivity」
   改为「互信息平台」并加边界注**——那是 orchestrator 先前的过度主张,本轮更正。

### 处置

- `RecordSymmetryNoGo`(已证未合)须将 `AssessedProvenance` 由 `FromRepo`
  改为 **`FromLiterature`** 并建 L 平面 note,方可落地。**先冻结再补表态是漏认前人成果的入口**,
  故该模块自证完起一直压着未推,本轮答案到才动。

## 本轮:**文献核对一条 no-go**(第 15 轮,2026-09-11)

自第 14 轮定价表以来,本线新增两条**条件切片**(均已冻结上 dev,物理输入在假设位、`axiom` 计数 0):

| 切片 | GID | 内容 |
|---|---|---|
| observer→objective | `D5/S3/Quantum/Information/OrthogonalRecordEntropy` | 记录片段两两正交 ⟹ `I = H(p)`,片段携带指针全部经典信息 |
| cross-species | `D5/S3/Quantum/Matrix/CrossSpeciesConsensus` | 共享**不可约**表示 + 等变自伴 ⟹ 该可观测量为标量,各 probe 读数相同 |

**把两组假设放在一起,它们相斥**——这是地图暴露的空白(第 3.6 条),也是本轮唯一的问题。

### Q1:下面这条 no-go,文献里已经有了吗?

> 设 `U : G →* Matrix n n ℂ`。若该表示**不可约**,则任何等变的自伴幂等 `P`
> (`P² = P`、`Pᴴ = P`、`∀g, P·U g = U g·P`)必为 `0` 或 `1`。
> 故**不存在非平凡的等变正交记录结构**,除非表示**可约**。
> 物理读法:**objectivity 要求指针基破坏那个共享对称性**。

论证极短(`P = r•1` 由已冻结的 `equivariant_selfAdjoint_eq_smul_id_of_irreducible` 给出,
`P² = P ⟹ r² = r ⟹ r ∈ {0,1}`),**正因为短,必须先问文献**(第 3.6 条 硬规则①:
候选进管线前先答「文献里有没有这条陈述」;第 3.7 条:写作即尽调,三态表态不许留白)。

**要回答的三件事**:
①这条陈述(或其等价形)在文献中是否已有?给出处;
②它与 Zurek/Korbicz 一系的 einselection、pointer basis、SBS 结果是**同一件事**、**推论**,还是**不同**?
③若已有,本仓应表 `literature-attested` 并建 L 平面 note;若确系新,表 `suspected-novel`。
**答「已知」是完全可接受的答案,不要为了让它显得新而含糊。**

### orchestrator 的数值读数(可复算)

commutant 维数:不可约(两个通用酉生成)**恒为 1**,25/25;
**判别力对照**:块对角可约时 **> 1**,25/25 ⟹ 存在非平凡等变投影。

### 本轮派发状态:**在飞,不得重投**

任务 ID **`333503a8-6b9d-4ad6-9d6e-2c927bfc875b`**,池 `chrono-chatgpt-pro-pool`。
runner 在 3600s 处超时退出(`QR_ROUND status=failed`),但**超时不等于失败**:
其判词原文为「still dispatched … Re-check later with `nyxid oracle result <id>`」,
实时查询 `nyxid oracle result` 返回 `Phase: waiting_response`。
**下一轮先用该 ID 取结果,不要重新派席**(重投会白费一次派发,且可能撞配额)。

**判在飞的判据(两者不可混)**:归档文件**开头**的 CLI 状态序列是**提交那一刻**的状态,
不随回包更新,以它判在飞是坏原材料;**实时 `nyxid oracle result` 的 `Phase:` 才是当前状态**。

### 同期在飞

形式化席 `nogo-1` 正在把上述 no-go 及其逆写成 Lean。**本轮的文献答案会决定它的
`AssessedProvenance` 表态**,故先问,不等它落地。

## 第 14 轮结算:定价表已出,**四项全部卡在物理输入**(2026-09-10)

Q1 问的是「给右栏四项定价,不选」。该席答得清楚,判词存于 `round-14-20260910T225553Z.md`。

### 定价结果

| 右栏项 | 障碍链是否变短 | 承重缺口 |
|---|---|---|
| observer → objective 桥 | **变短一环** | 二体偏迹 / 边缘态 / 互信息由「缺」变「已冻结」;objectivity 本身仍未出 |
| cross-species principle | 无变化 | 为何所有 probe 承载同一 active symmetry、表示为何不可约 |
| §17.1 / §18 量子统计层 | 无变化 | canonical quantization;`ρ_C ⊗ ρ_β` 是新的制备条件,非观察者假设的逻辑后果 |
| Einstein 方程 | 无变化 | 为何该张量场是普适几何变量、为何物质以同一应力-能量耦合进入、为何有 backreaction |

**跨四项的收敛结论:承重缺口全是物理输入,不是形式化能力。**
该席明写不把 Fierz–Pauli / spin-2 冒充成观察者假设的后果。

### orchestrator 复算(不是转述)

- 它独立核出的两个 `statement_id`(`sha256:b39b445e…`、`sha256:35bc509b…`)与我自算一致。
- 它引的障碍登记逐条对上:本文件 `:134`(objective「不声称已从 observer axiom 推出」)、
  `:135`(cross-species 需额外结构)、`:136`(§17.1/§18 须 owner 指定物理输入)、
  `CHARTER.md:42-43`(右栏五项各缺一条可点名的额外公理)。
- **一处归属错**:它把上述出处标成 issue #6298,实际在这两个仓内文件里(runner 内联喂给它的);
  **内容成立,归属不成立**。
- 它拒绝把在飞的 `corrtax-1` 倒算成已冻结成果——**这是正形**。

### 该席自划的核实边界(照录,不代它加强)

**#6298 的评论链它取不到**(公开页只返回主帖与评论入口)。凡依赖评论正文的前提,
它一律标 `ASSUMED-UNVERIFIED`,并明说不从主帖反推。**这是第二轮报同一件事**(第 12 轮亦然)
⟹ 承重状态不要放 issue 评论里,放本文件——runner 会内联,它读得到。

### 下一步的选择权仍在 τ=0

定价表说明四项**没有一项**因新冻结而变得「数学上够得着」;唯一松动的 observer→objective
松的是基础设施环,不是 objectivity 本身。**故仍不代选**(第 3.6 条)。
若要推进,τ=0 指定四项之一**或给出那条缺失的物理输入**;后者比选项更关键——
四项的承重缺口都是它。

## 本轮:**恢复派席**(第 14 轮,2026-09-10)

第 13 轮判「无靶」的具体前提——`相关-税恒等式` 所需的二体基础设施在 D5 命中全 0——
**已不成立**;基础设施是本线自己在这段时间补上的。第 13 轮判词在其当时读数下仍立,
不作废;本轮是新读数下的新结算(第 2.7 条)。结算评论见 issue #6298。

### 自第 13 轮以来本线新增的冻结(orchestrator 在 origin/dev 上逐条复算)

| 模块 | statement_id |
|---|---|
| `D5/S3/Quantum/Information/PartialTraceMutualInformation` | `sha256:b39b445e…` |
| `D5/S3/Quantum/Divergence/DualAccountFull` | `sha256:35bc509b…` |

前者给出 `partialTraceLeft/Right`、`*_posSemidef`、`trace_*` 与**单参数** `quantumMutualInformation`;
后者是 §17.2 第三条定理(互无偏语境下免双税 ⟹ 极大混态)。
源 atom `1e28ba01…` **仍为 `residual-open`**,未冒领整条。

### Q1(本轮唯一问题):给右栏四项定价,**不选**

已派 oracle 一席,问的**不是**「选哪一项」——那是第三档,第 3.6 条 明令机器不选。
问的是:**上述两个新冻结模块,是否使右栏四项中任何一项的障碍链变短?**

对 observer→objective 桥、cross-species principle、§17.1/§18 量子统计层、Einstein 方程,
逐项回答三件事:①它的障碍链上,哪些环现在已被仓内冻结定理覆盖(给 GID);
②哪些环仍缺,缺的是**定义**、**分析引理**还是**物理输入**;
③若要推进它,**下一个可形式化的最小单元**是什么。

**产出是给 τ=0 用的成本表,选择权不动。** 若某项的答案是「没有变化」,照直说;
四项全无变化也是合法答案,不要为了有产出而编造进展。

### 同期在飞的形式化席

`corrtax-1`,靶为 atom §17.2 明文所列的**相关-税恒等式** `I(系统:记录) = S(𝒫ρ) + D(ρ‖𝒫ρ)`。
orchestrator 亲验:秩一捏合 + 预测量相干复制膨胀下,d=2..5 共 160 例
**max|残差| = 6.661e-16**;判别力对照(`+D` 改 `−D`)**120/120 全败**。
承重细节:膨胀若改成经典 CQ 态,该式退化为 `I = S(𝒫ρ)` 而不成立。
**该靶不是第三档**,不需 τ=0 选方向。

## 本轮:**无靶,暂停派席**(第 13 轮,2026-09-10)

第 12 轮的判词**照收**;其四条引用已由 orchestrator 在 `origin/dev` 上逐条复算,全部成立。
结算评论:issue #6298。本轮**不派席**,理由是没有靶,不是没有席位。

### 结算读数(orchestrator 复算,非转述)

| 第 12 轮的引用 | 复算读数 |
|---|---|
| `…ThermalCoefficientFloor.sinh_le_self_mul_cosh_of_nonneg` | `D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.lean:42` 声明,第 71 行有使用 |
| 其冻结状态片 | 存在,`statement_id sha256:0340cb1ee26dcb999a070578ea6570e5293490432a9b01dd9d39dfc0c1d1428a` |
| runner 默认池 | `quantum-reality-round.sh:12` = `POOL="${2:-chrono-chatgpt-pro-pool}"` |
| round-10 归档非仍在飞 | 441 行;`waiting_response` 全文仅 1 次(表头);尾部为「未主张栏」 |

### 未复算(记 `ASSUMED-UNVERIFIED`)

第 12 轮称三种入口均取不到 #6298 的评论链——**未复现其取读失败**;
其对 pinned mathlib 的检索覆盖面亦未复算。

### 为何不派席

右栏余下四项(observer→objective 桥、cross-species principle、§17.1/§18 量子统计层、
Einstein 方程)**全部属第三档**,第 3.6 条:**机器不替人选第三档目标**。
第 3.2 条:**席位空闲不是派题的理由,有逃逸见证的靶才是**。
第 2.7 条 预算包络:连续投入无边际改进即触底,正解是换 Γ 或换目标。
**「这条该停」是本线允许的最好答案之一**;硬派一席只会产出一份复述。

### 本线同期的形式化产出(停的是派席,不是这条线)

- `D5/S3/Quantum/Divergence/GibbsVariationalIdentity` —— `log Z = ReTr(Hρ) + S(ρ) + D(ρ‖G)`,已合入 dev。
- `D5/S3/Quantum/Divergence/SpectralReadoutEntropyEquality` —— 谱读出保熵 ⟺ 读出矩阵对角,已合入 dev(PR #6896)。
- `observer-quantum-v1` 的 **131 个 atom 已全量分类**为 pointer / bind-only / needs-input / proposition,
  分类表随 #6896 落地,构成本线此后的选题面。

### 重启条件

**τ=0 点题**:指定右栏四项之一,或给出新的物理输入。写成新的 Q1 填进本文件,
跑 `tools/scripts/agent/quantum-reality-round.sh` 即续轮,**无需重建任何东西**。

## 本轮:**维持「无靶,暂停派席」**(第 12 轮,2026-09-10)

第 12 轮向 `chatgpt-pro-pool` 派出一席核对,该席**独立维持**第 11 轮的停止判定,
未被推动派题。判词与三条新读数存于 `round-12-20260910T185807Z.md`。
**结论未变,故 CHARTER 不动**;本节只记新读数。

### 新读数①:`waiting_response` 的词面命中不证明「仍在飞」

归档文件开头是 CLI 的状态序列(`dispatched / selecting_model / sent / waiting_response`),
**其后紧接判词正文与收尾**。以裸词面 `waiting_response` 判「该轮仍在飞」是把
**表头**当**终态**读,属第 8.4 条 所指的坏原材料。判在飞须看该文件是否含判词正文与收尾段,
或读宿主任务的哨兵退出码,不看表头词。

### 新读数②:runner 默认池不是 `chatgpt-pro-pool`

`quantum-reality-round.sh` 写的是 `POOL="${2:-chrono-chatgpt-pro-pool}"`;
第二参数可覆盖。故「坏池在默认路径上」不成立,不因此 hotfix。
**边界**:源码只证默认值,**不认证任一池的运行时健康**;文件存在性检查不是池健康检查。

### 新读数③:第 11 轮所引承重内容已核到

`D5.S3.Observer.Fluctuation.ThermalCoefficientFloor.sinh_le_self_mul_cosh_of_nonneg`
的声明与其冻结状态片 `Golden/Frozen/state/D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.lean.json`
均存在于所钉提交。

### 本轮的编号勘误

派发时 runner 被传入**主检出**作 lane-dir,其 `docs/reports/quantum-reality/` 只到第 10 轮,
故它算出 `round=10`,与本文件当前段(第 11 轮)冲突。该席当场指出此冲突。
真实轮次为**第 12 轮**,归档按此命名;主检出已恢复干净(第 6.1 条)。

## 本轮:**无靶,暂停派席**(第 11 轮,2026-09-10)

**判定与第 9、10 轮相同,且本轮无任何推翻**:三个原问题自第 8 轮起全部结算,
右栏余下四项**全部需要 τ=0 点题**(第 3.6 条:机器不替人选第三档目标);
前一轮已按第 2.7 条预算包络**显式停止定价**。**本轮未派任何席位。**

本轮做的是**核对既有引用**与**测量重启路径的可用性** —— 下面三条是新读数,
写在这里是为了让下一个接手者不必重推。结算全文见 `/issues/6298` 第 11 轮结算评论。

### 新读数 ①:「上一轮是否在飞」不能按裸 grep 判

`round-10-20260909T191620Z.md` 里确实命中一次 `waiting_response`,但它在**第 5 行**,
是 nyxid CLI 归档抄本的**表头**(`dispatched → selecting_model → sent → waiting_response`),
**不是**「本轮仍在飞」的状态 —— 该文件是 441 行的完整判词。
**按词面判会把一轮已完成的判词误读成在飞轮次**,进而错误地跳过结算。
判据应是**上下文**(有没有判词正文、有没有 `round-<N+1>` 工件),不是词面命中(第 8.4 条)。

### 新读数 ②:重启路径指向的池是活的,**不必修**

今日在素数线上实测到 nyxid 池健康度分叉(窗口=今日本机,**不外推**为长期状态):

| 池 | 读数 | 判 |
|---|---|---|
| `chatgpt-pro-pool` | 连续两次 `extraction_failure`(task `4e014c3d…`、`14fdf228…`) | **坏**;按纪律未第三次重投 |
| `chrono-chatgpt-pro-pool` | `Task is queued / Queue position: 2`,随后正常进入 `waiting_response` | **活** |

我本以为这会打断下节「重启条件」里那条 runner 路径,准备按第 5.5 条当场 hotfix。
**查完发现不用修**:`tools/scripts/agent/quantum-reality-round.sh:12` 是
`POOL="${2:-chrono-chatgpt-pro-pool}"`,默认就是活着的那个;坏池不在路径上。
该脚本另经 `:14-18` fail-closed 校验 CHARTER 与 OPEN-QUESTIONS 存在,
哨兵为 `QR_ROUND round=<N> status=dispatched|failed`。

**记这条是因为它本会是静默失效**:文档里的重启路径若指向一个「`status` 报 idle
但对任何输入都 `extraction_failure`」的池,要到重启当天才发现。现有读数证明它不指向那个池。

### 新读数 ③:本文件所引的两处位置仍成立(逐条复核,非转述)

| 被引项 | 复核结果 |
|---|---|
| Q1 逃逸见证 `sinh_le_self_mul_cosh_of_nonneg`「已落地」 | **成立**。`D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.lean:42`;`Golden/Frozen/state/…/ThermalCoefficientFloor.lean.json` 存在 |
| §18 需新物理输入,据 `QUANTUM-REALITY.md:1339` | **成立**。原文:「这是新的明确制备条件,不等于钟已处于每个条件位移基态组成的平衡子空间。」 |

**未在本轮重跑**的:前一轮那两条 bind-only 探针(`open`)。无新输入而重跑即重放(第 10.5 条),
故那两条仍是**前一轮的读数**,不是本轮新测。

---

## 战史:第 10 轮的定价与两条探针(保留,未被推翻)

**本文件仍不含待派的问题**,理由与第 9 轮相同:三个原问题都已结算,
右栏余下四项**全部需要 τ=0 点题**(第 3.6 条:机器不替人选第三档目标)。

**第 10 轮做的不是选题,是定价。** 章程为第三档规定的机器角色是
「GPT PRO 以 deep research 出文献地图与障碍登记」,本轮即此:
四项候选**各一份地形图**(A 需要的新输入 / B 文献走到哪一步 / C 最小可形式化切片 /
D 障碍分「可去项 vs 结构性盲核」两笔账 / E 代价以「要先建多少基础设施」计),
**不排序、不比较、不推荐**。判词全文见 `round-10-20260909T191620Z.md`,
该席开篇即自锁「不作选靶建议」。

### 四项的首个 Lean 切片(取自该轮 C 栏,**均未经 bind-only 探针**)

| 候选 | 拟议首切片 | 需要的新输入 |
|---|---|---|
| observer→objective 桥 | `orthogonal_record_trace_gives_sbs_consensus`(有限维记录模型) | 记录/环境分片结构;该席明写它**不声称已从 observer axiom 推出** |
| cross-species principle | `equivariant_selfAdjoint_eq_smul_id_of_irreducible` | 连接不同 species 的额外结构(该席固定了一个示例模型包,明标不表示推荐) |
| §17.1 / §18 量子统计层 | `thermal_weyl_characteristic_one_mode` | 单模 Fock/Gibbs 模型须先由 owner 指定为物理输入 |
| Einstein 方程 | `linearized_einstein_symbol_transverse`(`k^μ E_μν(k,h)=0`) | spin-2 模型输入 |

### orchestrator 的一条读数:**该待验项已跑,结果 `open`**(2026-09-10)

`equivariant_selfAdjoint_eq_smul_id_of_irreducible` 读着像实自伴版 Schur 引理,
第 10 轮结算时记为待验。**现已跑完 `tools/scripts/agent/bindonly-probe.sh`:**

```
BINDONLY_PROBE status=open lane=/Users/chronoai/trureturing-a392714r2 seconds=15
```

即该陈述 elaborate 通过,而 `exact?` **未能**从钉版 Mathlib 单项闭合它。

**这是单侧读数,不得读过头**(工具自己写明):`closed` 才是决定性的(命中即禁止派席);
**`open` 不足以据此派席** —— `exact?` 只试单项闭合,不排除数行 bind-only 组合。
它排除的只有一件事:**「钉版 Mathlib 一项就闭」**。

与手查一致:mathlib 的 Schur 在 `RepresentationTheory/FDRep.lean:158` 与
`CategoryTheory/Preadditive/Schur`,**均为代数闭域版**;有限维自伴谱定理另在
`Analysis/InnerProductSpace/Spectrum.lean`。实域上 Schur 只给除环(ℝ/ℂ/ℍ),
`A = aI` **不自动成立** —— 是「自伴」把它逼出来的。

**探针本身的两条边界(如实记)**:①首次跑在一棵**缓存未建**的 worktree 上,
真实错误是 `unknown module prefix 'Mathlib'` 而工具报 `statement-did-not-elaborate`,
我据此改了一个没错的陈述;该归因缺陷已修(`mathlib-unavailable-in-lane`,带三份真实工件的
预登记验证)。②第二次是真的陈述错(`⟪⟫_ℝ` 记号不在作用域),改用 `LinearMap.IsSymmetric` 后通过。
**上面那条 `open` 是第三次、在热树上、15 秒得到的。**

**对选题的意义**:四项中的 cross-species 一项,其拟议首切片**没有**在这一侧当场作废。
其余三项的切片**尚未探针**,不得据此推广。

### 第二条探针:Einstein 切片也是 `open`,**并就此停止定价**(2026-09-10)

```
BINDONLY_PROBE status=open lane=/Users/chronoai/trureturing-a372018 seconds=44
```

靶是 `linearized_einstein_symbol_transverse`(`k^μ E_μν(k,h) = 0`)。
签名把 Fierz–Pauli symbol 作为**假设**给出,而不是由我定义 ——
这样问的是「给定该 symbol,横向性是否钉版 Mathlib 一项即闭」,
而不是「我猜的定义对不对」。陈述 elaborate 通过,唯一错误是 `exact?` 未闭合。

**四项中已定价两项(cross-species、Einstein),两项未探,且我就此停止。** 理由:

1. 两次探针**都返回 `open`**,而 `open` 是信息量低的那一侧 ——
   只有 `closed` 是决定性的(命中即当场作废该切片)。连续两次没有作废任何东西,
   按第 2.7 条预算包络,这已经是**对着下确界加班**;
2. 余下两条里,**§17.1 / §18 那条需要先替它发明一个 Lean 可表达的替身**
   (钉版 Mathlib 没有 Fock 空间 / `a†a`)。那是**建模选择**,属该项「需要新物理输入」的一部分,
   不该由 orchestrator 单方面替 owner 做。observer→objective 那条虽是有限维、可表达,
   但按第 1 点,它的期望信息量同样低。

**这两条 `open` 能支持的结论只有一句**:那两条切片**不是**钉版 Mathlib 一项就能闭的。
**不支持**「它们可派」「它们有逃逸内容」「它们不是 bind-only」——
`exact?` 只试单项闭合,不排除数行 bind-only 组合。

### 重启条件(不变)

τ=0 指定右栏四项之一(或给出新的物理输入),把它写成新的 Q1 填进本文件,跑
`tools/scripts/agent/quantum-reality-round.sh` 即续轮。耐久件都在
`docs/reports/quantum-reality/`,无需重建任何东西。

---

## 战史:第 9 轮的判定(保留,未被推翻)

**本文件当前不含待派的问题。** 这不是遗漏,是第 8 轮结算的直接后果。

### 三个问题都已结算

| 问题 | 结算(见 `/issues/6298` 第八轮结算评论) | 之后 |
|---|---|---|
| Q1 §17 factoring | 靶成立。逃逸见证 `sinh_le_self_mul_cosh_of_nonneg`,orchestrator 亲自编译验证 `EXIT=0` | **已落地并合入 dev(PR #6517)** |
| Q2 下敏感度 | universal 版与 L3 族**不相容**(no-go);右栏第三项改写为「需独立 anti-screening / uniform-conditioning 原则」;该席主动收窄了判词边界 | 已结算 |
| Q3 第四个靶 | **「本线在无新公理输入下已到边际」** | **预登记的停止判据触发** |

### 为什么不硬凑第四个问题

第 8 轮逐项排除了四个最容易误报成「第四靶」的候选:

- **§19 再剥一层** —— 没有。`HiddenFieldResponse` 自己已把边界写死(无 remainder estimate、
  无 limiting PDE),三条 companions 明标 bind-only。
- **§17.2 谱和规则** —— substitution + finite sum,**逃逸见证为空**;
  为显困难去形式化 δ-分布积分只是扩大分析基建,不增加物理结论。
- **§17.1 本身 / §18** —— 都**不满足「无新输入」**:前者要正面形式化正则量子化与 Gibbs 态制备,
  后者卷内明写 `ρ_C ⊗ ρ_β` 是「新的明确制备条件」(`QUANTUM-REALITY.md:1339`,orchestrator 亲验)。
- **Q2 的紧致/单射子类** —— 数学上不需新逻辑公理,但断言真实模型落在该类
  **本身就是新的物理 / model-selection 输入**,观察者假设没给。

**右栏余下四项**(observer→objective 桥、cross-species principle、§17.1/§18 的量子统计层、
Einstein 方程三项)**全部需要 τ=0 点题**,属第 5⁵ 条第三档。
**机器不替人选第三档目标。**

### 重启条件(写清楚,免得下一轮又从零推)

本线**不是停摆,是走完了当前 Γ**。重启只需一件事:**τ=0 点题**,指定右栏四项中的一项
(或给出新的物理输入)。届时:

1. 耐久件都在仓里,`docs/reports/quantum-reality/`(CHARTER + 各轮判词,随 #6514 合入 dev);
2. runner 在 `tools/scripts/agent/quantum-reality-round.sh`(#6509);
3. 把点题写成新的 Q1 填进本文件,跑 runner 即可续轮。**无需重建任何东西。**

### 本轮不派席的依据

第 5⁵ 条:**席位空闲不是派题的理由,有逃逸见证的靶才是。**
第 2.7 条预算包络:连续投入无边际改进即触底,正解是换 Γ 或换目标,不是继续 grind。
CHARTER 的纪律条:**「这条该停」是本线允许的最好答案之一。**
