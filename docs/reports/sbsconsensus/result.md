# 正交记录条件切片：实施报告

本轮结算：**成**。完整条件定理已在 Lean 中证明，构建、报告、发射、冻结与
用户指定的 CI 内容检查层均通过。以下结算限于本轮实施交付。
产地：Codex implementation worker，使用 lean4 skill，主循环实施、单点自查，
零独立评审席。本报告不冒充 orchestrator 的独立评审或合并判词。

## 条件定理与物理边界

模块：`D5/S3/Quantum/Information/OrthogonalRecordEntropy.lean`。
有限指针分布 `p` 满足逐项非负、总和为 1；`rho i` 是任意有限维密度态。
具名且显式的物理假设为

```lean
hOrthogonal : Pairwise (fun i j => (rho i).1 * (rho j).1 = 0)
```

它对应 issue #6298 observer→objective 桥尚未采纳的
「正交记录/环境分片结构」输入。对正算子，零乘积表达支撑正交。
模块没有证明这条物理输入由 observer 条件推出，也没有将它登记为 axiom
或 instance；局部 CFC instance 只是 Mathlib 既有实连续函数演算实例，
不包含任何记录态或正交性条件。没有把熵分解或互信息结论放进假设位。

公开结果是：

1. `orthogonal_mixture_entropy`：
   `S(mixtureState p rho) = H(p) + Σ_i p_i S(rho_i)`。
2. `orthogonal_record_trace_gives_sbs_consensus`：
   `quantumMutualInformation (recordState p rho) = shannonEntropy p`。

`recordState` 是 `Σ_i p_i (|i><i| ⊗ rho_i)`，类型是 `DensityState (ι × n)`。
目标使用前置模块的单参数互信息定义；系统和片段边缘态均来自真实偏迹。
结论允许零概率、奇异密度态和任意有限指标类型，没有正定或非零权重限制。
Shannon 熵和 von Neumann 熵都用自然对数，单位一致。

这里形式化的是一个片段携带全部指针经典信息的熵等式。
测量仪器、观察者读取协议、多个片段的联合独立性以及从 observer 到实际
物理记录结构的推导均不在定理中。没有从互信息等式反推完整 SBS 结构。
这是一张「采纳该物理输入可以买到什么」的条件地形图。

## 判形、准入与复用检索

预登记在 `preregistration-v1.md`，提交 `7cb51cac8e`，早于 Lean 实施。
两条公开定理的 `proof_shape: content`；模块 `admission_basis: escape-witness`。
实际见证为正交混合态的熵可加分解，核心分析步骤是负 x log x 函数演算
对正交正算子的加性。完整互信息定理实际调用了该见证，非并列未连接的定义。

检索按 D5 → 钉版 Mathlib → 第三方形式化/文献推进。
Lean 为 v4.33.0，Mathlib pin 为
`db584cd6d46c92f209a44c0f1c829460d327499d`。

- D5 的 `MixtureEntropyUpperEquality` 有
  `mixture_entropy_eq_weighted_add_weight_entropy_iff_pairwise_disjoint_supports`，
  但它是经典分布定理，不能直接实例化成非交换密度矩阵的熵分解。
- Mathlib 的 `JointEigenspace` 提供共同本征空间分解，没有所需矩阵熵等式。
  复用了 `CFC.posPart_negPart_unique`，没有重证正负部分唯一性。
- QuAIR/Lean-QIT 固定版本 `c1d59b133b56e3d79efb11ee46a728d290f761f5`：
  实读 `QIT/Information/Entropy/Entropy.lean`（627 行）和 `Holevo.lean`（83 行），
  orthogonal/block/mixture 相关检索未得到可复用目标。
- physlib 固定版本 `889c09c66fb5f3c4a27182a43cafbed9e00b9d0a`：
  实读 `QuantumInfo/Entropy/Relative.lean`（2461 行），正交命中是支撑代数，
  没有命中目标熵分解。
- csd-lean4 固定版本 `13eda16971c66de4bc9f550e418dd4fdf59a5121`：
  范围说明区分 SBS 与熵平台，没有找到目标形式证明。
- 实际打开并读取 https://arxiv.org/html/1803.08936 ：Le 与 Olaya-Castro
  的论文附录 (19)–(28) 及其后的不交支撑计算给出所用的已知数学公式。
  只引用正交记录的正向熵计算，不依赖论文关于 strong independence 的逆向论断。
  Library 定位为 `D5/L/Quantum/le2019orthogonalrecords`。

结算是 searched-scope 内没有精确可复用形式化，不宣称全生态不存在。
数学公式是已知文献结果，不宣称新数学或新物理。因此没有触发预登记所说的
「找到既有精确形式化后降级」。没有复制第三方 Lean 证明，没有摄入自写理论卷。

## 证明连接

对正算子 `A B` 与 `A*B=0`，既有正负部分唯一性给出
`A=(A-B)⁺`、`B=(A-B)⁻`。函数演算的复合规则与实数正负部分恒等式推出
`cfc negMulLog (A+B) = cfc negMulLog A + cfc negMulLog B`。
再用 `Real.negMulLog_mul` 得到缩放项，以有限和归纳及迹的线性性证明
`orthogonal_mixture_entropy`。与既有 `vonNeumannEntropy` 的连接由
`entropy_eq_trace_cfc` 完成，奇异谱上的 log 由有限谱连续性处理。

指针态是对角秩一投影；证明其两两正交、幂等且熵为零。
联合态分量因指针正交而正交，应用熵分解及既有积态熵公式。
两条 `marginal*_mixture` 证明偏迹与有限混合可交换；结合既有积态偏迹公式，
系统熵为 `H(p)`，片段熵与联合态熵均为 `H(p)+Σ_i p_i S(rho_i)`。
展开既有互信息定义并消去相同项得到目标。

`utility: none` 对模块内所有声明适用：两条公开定理及私有辅助结论是任意
有限维一般等式，`mixtureState`/`recordState` 是带已证归一化的数学构造，
没有有界枚举、checker、numeric-reduction 或固定参数 certified-instance。
本地数值探针不进入 D5，亦不承载公理或证明。

## 数值复算

可复现程序 `numeric_probe.py`，种子 6298，NumPy 2.0.2。
维度 `(nP,dE)=(2,4),(3,6),(4,8)`，每组 80 个正交样本、40 个一般随机样本。
正交态由随机酉矩阵的不交二维列空间承载；一般态为归一化 Wishart 密度态。
程序构造联合矩阵并实算两侧偏迹，没有用预期熵公式代替观测量。

| 对照 | 本席实测 |
| --- | --- |
| 正交样本 | 240 |
| 最大 `abs(I-H)` | `1.0547118733938987e-15` |
| 一般随机样本中 `H-I > 1e-12` | 120/120 |
| 一般随机样本最小 `H-I` | `0.10033510189355399` |

本席结果与用户给出的舍入值不同，原样报告自己的读数。
这是有限浮点对照，不是去掉假设后的全称严格不等式证明，也不是 kernel 反例。

## 失败战史

1. 未找到已有量子混合熵定理；共同本征空间路线缺少可直接接上的矩阵熵接口，
   因此选择 Mathlib 正负部分唯一性与函数演算路线，没有重写谱分解理论。
2. 初版 CStarMatrix/Matrix 隐式转换与默认 CFC 参数导致 elaboration 失败。
   将实迹桥写明、显式给出函数演算参数以及 `ofMatrix.symm` 后消除。
3. 有限集合正交关系须用 `(s : Set ι).Pairwise`；指针投影谱须显式接入
   `isIdempotentElem_iff_spectrum_subset`。这些是接口错误，不是改变数学假设。
4. 最后两处偏迹线性性错误是把 `Finset.smul_sum` 的隐式参数当显式参数传入；
   改为 `Finset.smul_sum.symm` 后完整定理编译通过。
5. 失败 elaboration 时编译器曾打印 `sorryAx`，那些版本未被记作证明完成。
   最终两条定理打印的 axiom 闭包均为 `propext, Classical.choice, Quot.sound`。
   未发生作业被杀；未启动叠加构建；两个用户指定的高内存模块没有被修改。
6. 一次外网 raw.githubusercontent 请求退出 56，后用 authenticated GitHub API
   读取固定版本。失败请求不算有效来源。

最初串行构建同时补建了该树三个缺失前置；后续只重建本模块。
仅删过本模块的 olean/trace 以令串行器重建改动；没有清理全树缓存。
本模块仍有一个未使用 `[DecidableEq ι]` 的 Lean linter 警告，不影响类型或公理闭包。

## 验收收据

完整证明提交：`7ebe6ef00d`；熵分解首个成功单元：`3c88eac2cb`。
完整构建收据：`SERIAL_LEAN status=complete built=1 failed=0 missing=1`。
`make lean-report` exit=0，报告内容地址
`sha256:8c237ecf1b26ccc518a544dc15aeb417329cd953be4599d17cd86997c50c07db`。
全部本模块声明的 axiom 并集为 `Classical.choice, Quot.sound, propext`，无 `sorryAx`。
`make emit` exit=0，生成一篇 Blueprint。
`make deposit-uncovered` exit=0，`LEDGER_ALIGN ... added=1 ... conflicts=0`，
末行 `PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED`，GID 为完整目标、`reason=NO_ATOM`。
未创建 atom 或 coverage 边。
冻结事件为
`Golden/Frozen/accepted/a781b508b4b36e59cbea0478c5decac01cf8d8e6d54641e5bc8b72157173e05b.json`，
模块 statement_id 为
`sha256:cee4de5737b3d26067acc3c6c4c089653789f1fe531303dd14a9f52f71448430`。

用户指定的 `scribe-content-checks.sh` 使用精确 merge-base
`a6443848fc7b2dc460a3e4cf54e372e6bf3766a9`，exit=0，判词为：

```text
DESCRIBE_STATUS case=DESCRIBE-NODES status=classified nodes=11105 suspected_novel=0 formula_content_slots=68 formula_statements=32 red=0 observe=4996
```

`^RED` 为零命中；OPEN projection 与 OBSERVE 未被计作失败或绿灯替代物。
本地门链不是独立语义评审，亦不是远端 CI/合并状态声明。

本次完整命令日志位于 runner attempt：
`/var/folders/wv/ht3wzsj138b4sxl3q4t0xdr40000gn/T/consensus-rnd/sshx/sbs-1/attempt-1/`，
对应 `lean-detail.log`、`lean-report.log`、`emit.log`、`deposit.log`、
`scribe-content-checks.log`。`lean-detail.log` 保留历次失败及最终成功，不把历史
失败误读为最终 axiom 闭包；最终报告身份与闭包见 `proof-provenance.json`。

两条手写公开数学定理的身份如下；自动生成的 congr_simp 与局部既有 CFC
实例转接不作为额外数学交付。完整接口身份见 `proof-provenance.json`。

| GID | statement_id | proof_shape | admission_basis |
| --- | --- | --- | --- |
| `D5/S3/Quantum/Information/OrthogonalRecordEntropy.orthogonal_mixture_entropy` | `sha256:0de48f59cd31d9966c14049a4fee24ce1aba95b2eea9f3980ae6ebdf93019620` | content | escape-witness |
| `D5/S3/Quantum/Information/OrthogonalRecordEntropy.orthogonal_record_trace_gives_sbs_consensus` | `sha256:fc390ce9d27486ba5f8163e95243d66de435f386cc0bbc97d26c89e9af49fe60` | content | escape-witness |

逐定理前置核算按源码实际使用列举，不冒充自动 elaborated 依赖 census：

- 熵分解的数学证明调用本模块新分析引理及 Mathlib，没有直接调用旧冻结 D5
  定理；它的已冻结定义接口是 `DensityState`、`vonNeumannEntropy`、`shannonEntropy`，
  各 GID 与 statement_id 已逐项记录于 JSON 的该定理条目。
  escape_witness 是本结论及其正交 CFC 加性证明；删除该分析后，现有定义和
  经典熵定理的改名、展开、实例化不能产生非交换正交混合态熵分解。
- 互信息定理的活路径调用新 `orthogonal_mixture_entropy`，并直接使用以下三条
  旧冻结定理。共享定义接口和模块内偏迹/指针态辅助结论也在 JSON 单列。
  escape_witness 是实际被调用的正交熵分解；该物理假设用于片段混合态这一步。

| 互信息定理直接使用的旧冻结定理 GID | statement_id |
| --- | --- |
| `D5/S3/Quantum/Information/PartialTraceMutualInformation.vonNeumannEntropy_productState` | `sha256:c282fec63ac9abe78f2927a141bb4576d82585b91d0085e4a160f9a9b6efd042` |
| `D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalRight_productState` | `sha256:cafa71401e68066df56033c6466fde4878d18496f8ef43e8f2600b6a0074ef76` |
| `D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalLeft_productState` | `sha256:a9840d043b5a8d2b0917f100f01c7f02a319c9363b7ba18fc4050e59e2321393` |

落点复查使用各目录直接普通文件数，Blueprint 排除 `.md`：
`D5/S3/Quantum/Information` 为 4，Blueprint 对应目录为 4，`Library/Quantum` 为 19，
均低于 SL-003 上限 48。Lean 所有行均不超过 100 字符，七行头部次序正确。
新模块 generality G；两个直接 D5 import 都为 G；Quantum 在 `Meta/domains.yaml` 已注册。

起点及开工 merge-base：`a6443848fc7b2dc460a3e4cf54e372e6bf3766a9`。
