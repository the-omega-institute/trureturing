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
