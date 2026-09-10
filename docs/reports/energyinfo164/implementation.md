# 定理 164.1 实施报告

**结算：成。** (164.1) 四步完整证明，串行构建、Lean report、发射、冻结与指定
CI 同层内容检查全部通过。此结算采用用户的 implementation 判据，不表示 PR 已合并。

产地：Codex 主循环，使用 lean4 skill；runner implementation 席，零独立评审席。
本报告的数值与本地门读数均由本席亲跑。原 orchestrator 数值只作输入，未照抄。

目标：quantum-reality atom
`0b75ef93a42867b46dad6346602e61b3e0ddd972090c84dc472bf3e38758283b` 的 (164.1)。
形式化真源：`D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.lean`。
构建起点：`ea50faf34c76b4e446b2a9e64d3f7ad0d7f0867a`，Lean 4.33.0，
Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`。

## 数学交付

四步均已证明。HA、HB 为任意有限非空复矩阵空间上的厄米物理 Hamiltonian，
betaA、betaB 为实数。`thermalState H hH beta` 直接应用既有
`gibbsState (-beta • H)`，不是新建 Gibbs 理论。

初态 `rho : DensityState (A × B)` 的假设恰为
`marginalRight rho = thermalState HA hHA betaA` 和
`marginalLeft rho = thermalState HB hHB betaB`。
`marginalRight` 留 A、`marginalLeft` 留 B。末态直接定义为
`unitaryConjugateState U hU rho`，`hU` 是联合空间的 unitary group 成员证明。
没有乘积态、初始互信息为零、总能量守恒或末态满秩假设。

1. `gibbs_relative_entropy_energy_difference`：对任意末态，
   D(final || gamma) = beta (E(final)-E(initial)) - (S(final)-S(initial))。
   直接应用 `gibbs_variational_identity` 两次，以 D(gamma || gamma)=0 消去 log Z。
   `log_gibbs_state` 已被该冻结 Gibbs 恒等式消费，不重证矩阵对数。
2. `von_neumann_entropy_unitary`：任意酉共轭保总熵，包括奇异密度态。
   在公开 `entropy_production_coherence_deletion_identity` 中取迭代序列，
   对 U,rho 取第零步；另对 1,U rho U* 取第零步。两个等式右侧完全相同，
   消去共同退相干熵项即可。没有引用私有声明的编译名，也没有重证其 CFC 分析。
3. `marginal_entropy_change_eq_mutual_information_change`：上述保熵结论代入
   单参数 `quantumMutualInformation` 的定义，得 Delta S_A+Delta S_B=Delta I。
4. `energy_information_identity`：两次应用第 1 条，再代入第 3 条，合成完整 (164.1)。

`meanEnergy` 与 `thermalState` 两个定义由第 1 条实际连接并在主定理消费。
没有用定义展开的同义反复冒充交付。四个手写公开定理均有实质关联，
未把任何待证能量或熵等式移入假设。

## 判形与准入

`preregistration.md` v1 保留用户拟议。API 阅读发现第 3 步可由公开冻结结果
经实例化、投影、定义展开和 ring 得到，故在写 Lean/数值脚本之前登记并提交 v2
（`ba7bac4cb0`）。不将该步骤误报为新分析见证。

全部四个手写公开定理：`proof_shape: bind-only`、`escape_witness: none`、
`admission_basis: atom-required-bridge`。准入所据是该 atom 明文要求的两侧连接，
具名下游消费者是预登记的 `energy_information_identity`。
`utility: none`：所有 Lean 结果均对任意有限维度和任意满足原假设的状态量化；
数值实验不进入 Lean，未交付枚举、检查器、数值归约或认证实例。
其它 utility 字段为 not-applicable(kind=none)。

| 公开定理 | 活路径与直接前置（方向：消费者 → 前置） |
| --- | --- |
| gibbs_relative_entropy_energy_difference | → 冻结 gibbs_variational_identity；使用冻结 gibbsState、quantumRelativeEntropy、vonNeumannEntropy |
| von_neumann_entropy_unitary | → 私有 pinching_after_unitary → 冻结 entropy_production_coherence_deletion_identity；使用冻结 unitaryConjugateState、basisPinchingState、vonNeumannEntropy |
| marginal_entropy_change_eq_mutual_information_change | → von_neumann_entropy_unitary；展开冻结 quantumMutualInformation、marginalRight、marginalLeft |
| energy_information_identity | → gibbs_relative_entropy_energy_difference（A、B 各一次）与 marginal_entropy_change_eq_mutual_information_change |

上述每个具名冻结前置的完整 GID 与实际 `statement_id` 位于
`kernel-audit.json` 的 `named_frozen_prerequisites`；每个新声明的实际身份、
公理闭包、源码 SHA 和 import 集合位于 `module_report`。这些字段来自 canonical
Lean semantic report，不以文本中 sorry 的计数代替编译。路径表说明的是具名
证明前置，不冒充由 import 图计算出的全部表达式常量闭包。

伴随声明对应义务：第 1 条对应 atom Gibbs 证明段；第 2、3 条对应联合酉保熵
及 Delta I 段；其消费者为主定理。自动生成的 congr_simp / proof 声明不是
独立交付。主定理保持 `+ I(final) - I(initial)`，没有丢失初始关联项。

## 独立数值读数

复现：`python3 docs/reports/energyinfo164/numerical_check.py`。
NumPy 2.0.2，seed=1641；维数配对 (2,2)、(2,3)、(3,2)、(3,3)。
41 个有关联初态与 20 个乘积对照，共 61 例；没有筛掉计算失败的样本。
每个有关联初态由归一化无迹厄米 X,Y 构造
rho = gammaA tensor gammaB + epsilon X tensor Y，
epsilon = 0.35 lambda_min(gammaA tensor gammaB)/norm(X tensor Y)。
因此正性有明确余量，而两侧偏迹的扰动在数学上为零。
随机 U 为联合空间复高斯矩阵的 QR 酉矩阵；Hamiltonian 非对角，beta 可正可负。

| 判据 | 本席实测 |
| --- | ---: |
| 主恒等式 max abs residual | 2.3314683517128287e-15 |
| Gibbs 边缘 max abs error | 6.662297251776943e-16 |
| 41 个关联初态中 min I(initial) | 7.447127611848181e-5 |
| 将 +Delta I 换成 -Delta I，超过预登记 1e-8 阈值 | 41/41 |
| 反号对照 min abs residual | 7.475938776877834e-3 |

单边残差、总熵残差、Delta I 残差、酉性残差和初态最小特征值逐例存于
`numerical-results.json`。这些是浮点诊断；Lean 的全称证明才是数学交付。
与用户给出的 3.553e-15 不同，是独立固定种子试验的读数，不声称逐例复现
未提供的 orchestrator 随机数流。

## 尽调与边界

已完整读取 CLAUDE.md、agents/CONTEXT.md、用户四个指定模块及实际使用的
EntropyProductionCoherenceDeletionIdentity。Gibbs 和熵/偏迹前置全部直接复用。
第三方有界检索及命中记录见预登记；未声称搜索穷尽。
Micadei 等 2019 年文章的 Crossref 与 Nature 正文已打开；Methods (6)、(7)
与 (8) 后段支持此证明链。文献 note 只绑定一个 URL；定位段包含该 URL 原文。

本靶不包括同 atom 后面的 (164.2)、热流符号、关联非负性、热化或实验论断。
按用户指定走 deposit-uncovered，不将整个复合 atom 标为已覆盖。
零独立评审、零远端 CI 判词；本地门通过不得冒称 PR 已合并。

## 门读数与失败战史

- 首次串行构建：EXIT=0；`SERIAL_LEAN status=complete built=9 failed=0 missing=9`。
  新模块首次即编译通过，四个打印的公理闭包均为标准三公理。
  先提交源码（`a1dc8093a8`）使 serial-lean 的 HEAD 扫描纳入新模块。
- `make lean-report`：EXIT=0；热缓存 `status=present`，project/mathlib 均 warm；
  delta recheck=2。新模块 report 的 11 个声明全为 std3，不含 sorryAx。
- route 首次用绝对 /tmp 路径，CLI 按 repository-relative 契约拒绝；
  改用本目录 `route.json` 后 EXIT=0，返回路径与实际 Lean 地址完全一致。
- 数值首次输出：NumPy int64 不被标准 JSON 编码器接受；改为 Python int 后
  固定种子重跑全部 61 例通过。JSON 改为每例一行，避免超长文件行数。
- 发射首次 EXIT=2：Library loader 拒绝 `url: null`，并连带报 3 条文献悬空。
  已按指定模板改为 `doi: null` 与非空 DOI URL；定位段含同一 URL。
  未修改解析器或任何门。Scribe 词法常量在发射前按真实 DSL 校正。

## 最终门链

- 修正后的 `make emit`：EXIT=0；恰好 1 个新增 Blueprint，四条声明显示 std3。
- `make deposit-uncovered`：EXIT=0；`LEDGER_ALIGN selectors_considered=4043
  changed=0 added=1 unchanged=4042 conflicts=0`；终态为
  `PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED`。内部复用 cached Lean report，再运行
  deposit-header-check、emit 和 ledger-align，未运行裸 make lean。
- 冻结状态 `statement_id`：
  `sha256:81e5d4c3c54523623d1cb3ffa11631f8043a86425e6161a03f1519b3710777e3`。
  accepted 事件：`4c490c983069ff05e10ca489072a7326c77a6e94654b924f146d9b1a90fd5fbc`。
  冻结产物即时提交：`cde44cc563`。
- 用户指定的 `scribe-content-checks.sh`：EXIT=0；第三参数为实际
  `git merge-base HEAD origin/dev` = `ea50faf34c76b4e446b2a9e64d3f7ad0d7f0867a`。
  判词：`DESCRIBE_STATUS case=DESCRIBE-NODES status=classified nodes=11097
  suspected_novel=0 formula_content_slots=66 formula_statements=32 red=0 observe=4994`。
  `^RED` 零行；4994 条 Observe 不冒充红或绿的判词。
- 落点复核：Lean Information 3 文件、Blueprint Information 3 个计算名额
  （不计 .md）、Library/Quantum 18 文件，均小于 48。Quantum 已注册为 S3；
  三个直接 D5 import 均为 G。新 Lean 145 行，最长行 94 字符，七行头合法。
- `git diff --check`：EXIT=0。无冻结前置、工具、理论卷或消化 atom 改动。

数学缺口：无（限定于 (164.1)）。失败仅为已修正的 JSON 序列化、route 路径
与 Library URL 空值格式；未发生构建被杀，因此不需要孤儿清理。
未运行全量 engineering 或远端 required CI；本次没有修改 harness。
分支已推送，独立评审与 PR 生命周期交由调用方继续。

原始日志与 result.json/completion.sentinel 由本席保存到用户指定的
`/var/folders/wv/ht3wzsj138b4sxl3q4t0xdr40000gn/T/consensus-rnd/sshx/einfo164-1/attempt-1`。
结构化核验、数值与叙事源均已提交；没有将原始全库日志写入仓库。
