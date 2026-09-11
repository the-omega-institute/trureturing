# 量子观察者假设:已推出的物理结构(形式化地形图)

本文是 issue #6298 研究线的**单一入口**。它只做三件事:说明**已推出什么结构**、
**每条结构依赖哪条假设**、**还缺什么以及缺的是哪一类东西**。

**这不是规范真源**(那是 `CLAUDE.md` 与 spec),也不复述各模块正文——
每行给 GID 与 `statement_id`,读者据此可自行复算(第 4.2 条 一名一址)。
**凡未冻结者一律不列**;在飞、已证未合、拟议名目都不进本表。

## 一、已推出的结构

下表每行的读法:**在「所需假设」成立的前提下,观察者假设给出「结构」**。
所有假设都在 Lean 的**假设位**,不是 axiom——各模块 `axiom` + `instance` 计数为 0。

| 结构 | 所需假设 | GID | statement_id |
|---|---|---|---|
| 记录片段达到**互信息平台** `I = H(p)`(**不是**完整 objectivity) | 片段态两两正交、CQ 态 | `D5/S3/Quantum/Information/OrthogonalRecordEntropy` | `sha256:cee4de5737b3` |
| 所有 probe 对同一可观测量读数**一致** | 共享**不可约**表示 + 可观测量等变 | `D5/S3/Quantum/Matrix/CrossSpeciesConsensus` | `sha256:672f7703c7fa` |
| **等变幂等记录族的条数 ≤ `Σ_b m_b`** | commutant 半单;记录族**非零、完备、两两正交、与共享作用逐个对易**(`m_b` 是该 commutant 的 Wedderburn 块尺寸) | `D5/S3/Quantum/Matrix/RecordCapacity` | `sha256:07d5f082f3b7` |
| **等变幂等记录族的条数 ≤ `Σ_b m_b`,不再需要半单性假设** | 表示**酉**(`∀ g, U g ∈ unitary`);记录族非零、完备、两两正交、与共享作用逐个对易。**群可任意**——无有限性、无紧性 | `D5/S3/Quantum/Matrix/CommutantSemisimple` | `sha256:50a83d557929` |
| 谱读出**保熵 ⟺ 读出矩阵对角** | 有限维、酉基变换 | `D5/S3/Quantum/Divergence/SpectralReadoutEntropyEquality` | `sha256:733b32d4e8cb` |
| 相关 = 记录账面价值 + 被杀相干(`I = S(𝒫ρ) + D(ρ‖𝒫ρ)`) | 记录侧取**预测量相干复制**膨胀 | `D5/S3/Quantum/Information/CoherentCopyCorrelationTax` | `sha256:515e26b6d8e1` |
| 免双税 ⟹ **极大混态** | 两语境互无偏、秩一 | `D5/S3/Quantum/Divergence/DualAccountFull` | `sha256:35bc509bf4b8` |
| 有初始关联时的能量-信息恒等式 | 两边缘恰为 Gibbs 态、联合酉演化 | `D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity` | `sha256:81e5d4c3c545` |
| `I(A:R) + I(A:B) = 2S(A)` | `ABR` 纯态 | `D5/S3/Quantum/Information/InputInformationBalance` | `sha256:380463defe87` |

> **边界(第 15 轮文献核对后补,不得省略)**:互信息平台 `I = H(p)` **不能单独升级为
> objectivity 判据**。Le 与 Olaya-Castro(2019)明确区分**互信息平台 / strong quantum
> Darwinism / SBS** 三层;Korbicz 等(*Quantum origins of objectivity*, PRA **91**, 032122, 2015)
> 的 SBS 定义**不要求**支撑投影与任何共享群作用对易。仓内该定理带有具体的 CQ 态与正交支撑前提,
> **脱离这些前提使用即为冒领**。

**基础设施**(上表的共同前置,本身不是物理主张):
`Information/PartialTraceMutualInformation`(`sha256:b39b445e3b81`,偏迹保密度态 + 单参数互信息)、
`Divergence/GibbsVariationalIdentity`(`sha256:a2a5b66e92f7`,`log Z = ReTr(Hρ) + S(ρ) + D(ρ‖G)`)。

## 二、这张图上唯一的**定量律**(经典代数结果的形式化实例)

> **给定共享表示 `U`。若其 commutant 半单,则存在取自该 commutant 的 Wedderburn 分解的
> 块尺寸 `m_b`,使同一组尺寸对每个非零、两两正交、求和为单位、且逐个与 `U` 对易的幂等族 `P`
> 都满足 `card I ≤ Σ_b m_b`。**

**来源表态:`literature-attested`。** 该计数界是结构定理(Artin–Wedderburn)配 Jordan–Hölder
的标准推论——把正则模的组成长度作为预算即可导出,详见
`D5/L/Quantum/mathlib2026recordcapacity`。**本仓的贡献在形式化与接口**
(以真实 commutant 为接口运输幂等族,并把同一组块尺寸用于所有合格记录族;
仓内版本甚至不假设两两正交),**不在数学内核**。
第 16 轮之前本行记作本仓来源,那是**漏认前人成果**(第 3.7 条),已更正。

**本行不主张、也推不出的两件事(第 16 轮核对后补,不得省略)**:

1. **它不认定哪些幂等元是「记录」,也不给出 objectivity。** Lean 声明只约束**指定共享作用下
   的等变幂等分解**;其中没有态、没有制备、没有环境分片、没有任何 objectivity 判据。
   它可以约束**另由物理模型识别为记录**的那些幂等元,但完成不了那项识别。
2. **`m_b` 是 commutant 的 Wedderburn 块尺寸,不是原表示各不可约分量的重数。**
   把两者等同**未被形式化**——模块自己的正文就写着
   「Identifying these sizes with multiplicities of a separately specified irrep
   decomposition is not formalized here」。

「这张图上唯一」是**栏目内**的范围限定(见第四节:本节只收统一多条结构的定量律),
不是首创声明;文献已知不否定该范围内的唯一性,但**它不得被当作本线新发现的物理定量律**。

它与本线此前那条 no-go 的关系仍然成立:commutant 为标量(单块、`m = 1`)时 `Σ_b m_b = 1`,
故非平凡的等变正交记录族不存在——那是本律的边界值,不是独立障碍。

**推论(权衡,非选择)**:要 `k` 条并存的等变正交记录,commutant 就必须带够块尺寸;
commutant 为标量就只能有一条。**这是定量代价表,不是待决选项。**

## 三、还缺什么,以及缺的是哪一类

| 缺口 | 类别 | 说明 |
|---|---|---|
| objectivity 本身(而非「片段信息完整」) | **物理输入** | 需记录/环境分片结构为何出现,观察者假设不给 |
| cross-species:为何所有 probe 共享同一 active symmetry | **物理输入** | 见 `OPEN-QUESTIONS.md` 第 14 轮定价表 |
| §17.1 / §18 量子统计层 | **物理输入** | canonical quantization;`ρ_C ⊗ ρ_β` 是新制备条件 |
| Einstein 方程 | **物理输入** | Fierz–Pauli / spin-2 本身即新输入,非观察者假设的后果 |

**剩下四项缺的全部是物理输入,不是形式化能力**(原列第一项「半单性由酉性导出」已于 `CommutantSemisimple` 闭合,见第一节;其路线是 ⋆-闭包而非 Maschke,且反例 `not_all_integer_matrix_commutants_semisimple` 已一并冻结,证明酉性是承重假设)(第 14 轮定价表的结论,orchestrator 已复算)。
按 第 3.6 条,**机器不替人选第三档目标**:采纳哪条物理输入由 τ=0 决定;
机器负责把「若采纳它,买到什么」写成可查的账——本表第一、二节即是。

## 四、维护约定

- 新增一条冻结结构即在第一节加一行,**给 GID 与 `statement_id`**;
- 第二节只收**由多条结构统一得出的定量律**,不收单条定理;
- 第三节的「类别」必须是 `数学` / `物理输入` 二者之一;写不出属于哪类,说明该缺口还没想清楚。
