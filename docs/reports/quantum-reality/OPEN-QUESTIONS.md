## 本轮:**仍无待派的靶,但四项候选已定价**(第 10 轮,2026-09-10)

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
