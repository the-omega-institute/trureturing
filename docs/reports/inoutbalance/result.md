# 原输入信息的内外平衡：实施结果

结算：**成**（本次 implementation 的数学与本地门链判据）。
主定理 `D5/S3/Quantum/Information/InputInformationBalance.input_information_balance`
证明同一个纯 ABR 密度态的实际边缘满足 `I(A:R)+I(A:B)=2S(A)`。
没有将互补熵相等放进假设，没有三个彼此独立的状态参数。
本报告不主张 PR 已合并或独立评审已完成。

产地：Codex 实施席，使用 lean4 技能；单席实施与自查，零独立评审席。
用户提供的 orchestrator 读数与本席重算读数分别保留。

## 目标、判形与准入

源为 `quantum-reality` atom
`1a71353ff4dfdc935a0206eb30fa29832f961bb7548537ca4530dcfb91c0409f`。
question_answered：纯态的输入信息是否按该 atom 的两条互补熵等式平衡；
预登记见 `preregistration.md` 与实现前的降级版本 `preregistration-v2.md`。

| 公开定理 | proof_shape | admission_basis | escape_witness |
| --- | --- | --- | --- |
| `pure_complementary_entropy` | bind-only | rule-11-upstream-wrapper | none |
| `input_information_balance` | bind-only | rule-11-upstream-wrapper | none |

拟议的原创见证因精确上游命中而撤销。互补熵的来源是 physlib 的
`Sᵥₙ_of_partial_eq`、`Sᵥₙ_pure_complement`，采用 A17.2 的来源注明移植。
这份包装的必要性是 atom 明文所需的 `S(AR)=S(B)` 与 `S(AB)=S(R)`，
而本仓 API 使用 DensityState/CStarMatrix/迹熵，上游使用 MState/Ket/谱熵。
该接口差异与三体类型重分组均如实记为 API 工作，不申报原创数学内容。

方向为消费者 → 前置：主定理 → 互补熵定理；主定理 →
`ab_retains_A`、`ar_retains_A`、`ar_retains_R`、`ab_retains_B`。
互补熵定理 → 非零特征根一致性 → 矩形乘积特征多项式交换。
这几条边均在返回证明中使用，没有插入再丢弃的合取分量。
`IsPure`、`relabel`、`stateAB`、`stateAR` 的定义被上述证明实际消费。
编译器生成的 `relabel._proof_1` 是 relabel 的正性证书，按 bind-only 的
伴随证明处理，不作为独立成果。

逐定理的 GID、statement_id、局部常量展开后直接冻结依赖的 GID 与
statement_id 见 `declarations.json`。这些依赖通过 Lean 环境中的
`ConstantInfo.value? (allowOpaque := true)` 与 `Expr.getUsedConstants` 取得，
仅递归展开本模块常量；原始边在 attempt 的 `dependencies.log`。
该读数证明常量边，不冒称机器已经裁决全部活路径或判形语义。

utility: `none`。全部声明处理任意有限载体、向量、矩阵或状态，
既无有界枚举，也无 checker、数值前提归约或已认证固定实例。
其余计算性用途字段均为 not-applicable(kind=none)。

## 检索与来源

dominating_theorem_search：**found（第三方），not-found-in-searched-scope（D5 与钉版 mathlib）**。

- D5：检索 `vonNeumannEntropy`、`partialTrace`、`Schmidt`、纯态/边缘/熵组合；
  核对 PartialTraceMutualInformation、PureStateHandshake、CoherentHistorySchmidt
  等候选。历史态的特定 Schmidt 权重、Bell 的特例不是一般互补熵定理。
  收尾时再次在整个 D5 检索相关 entropy/pure/marginal 声明，未见其他一般命中。
- 钉版 mathlib：`db584cd6d46c92f209a44c0f1c829460d327499d`，Lean v4.33.0。
  核对 SingularValues、HermitianFunctionalCalculus、Charpoly/Basic。
  直接复用 `Matrix.charpoly_mul_comm'`、`Matrix.charpoly_transpose`、
  `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`；未重证这些定理。
- 出网能力实测：`gh api -X GET search/code -f 'q="entropy" "pure" language:Lean'`
  成功，total_count=239，读取默认第一页 30 项，不声称穷尽。
  下载并阅读 physlib、Lean-QIT 的 PureEntanglement、csd-lean4 的 Entropy 候选。
  physlib 精确版本为 `889c09c66fb5f3c4a27182a43cafbed9e00b9d0a`，
  `QuantumInfo/Entropy/VonNeumann.lean` 含完整非零根证明。
  Lean-QIT 的候选转引另一条互补熵定理；未采用，未声称审计其闭包。
- physlib 的 toolchain 与 mathlib rev 均与本仓相等；A17 直接依赖准入仍 open，
  沿仓内已有先例用 A17.2 移植，保留版权、LICENSE 与钉版退役条件。
  上游根树无 NOTICE。Library note 的 doi/url 两键齐备，绑定 URL 原文
  位于 Verified locator。迹熵到谱和的局部计算沿用已导入模块注明来源的
  csd-lean4 计算；其相应 helper 是私有的，本次没有依赖其编译器私有符号名。

## 数值复算

`numerics.json` 保存 NumPy 2.0.2、default_rng(462)、自然对数的读数。
每种维数 `(2,2,2)`、`(2,3,3)`、`(3,2,4)` 各 50 个独立复高斯归一化向量，
通过重排系数矩阵并乘其共轭转置求约化态，eigvalsh 求熵。
仅保留大于 `1e-14` 的特征值计算 `-p log p`，判别阈值为 `1e-10`。

150 例 max|残差|=`7.771561172376096e-16`；另取 80 个 `(2,2,2)` 纯态，
将右端改成 S(A)，80/80 失败，min|残差|=`0.20009579825312995`。
用户的 `1.110e-15` 是不同抽样读数，不要求浮点结果逐字相同。
数值实验只作探针，正式证明不调用数值 oracle 或 native_decide。

## 核验与冻结

起点及本次精确 merge-base：`0959718b31ddd1d663683c2d71ac23c32ccb6e8d`。
route 返回 `D5/S3/Quantum/Information/InputInformationBalance.lean`，域 Quantum 已注册 S3。
新模块 generality=G，唯一直接仓内 import 为 generality=G 的前置模块。
目录计数（Blueprint 的 .md 不计）：D5 Information=5、Blueprint Information=5、
Library/Quantum=20；均低于 48。Lean 源码每行不超过 100 字符。

| 验证 | 结果 | attempt 日志 |
| --- | --- | --- |
| serial-lean | exit 0，status=complete built=1 failed=0 missing=1 | serial-lean-2.log |
| make lean-report | exit 0；新模块 20 个声明仅标准三公理 | lean-report.log |
| make emit | exit 0；新增 Blueprint 已阅读 | emit-1.log |
| make deposit-uncovered | exit 0；added=1 changed=0 conflicts=0 | deposit.log |
| scribe-content-checks.sh（精确 merge-base） | exit 0；status=classified red=0 | scribe-content-checks.log |

正式 report 内容地址：
`sha256:13857c67d3a842e8cf2b6a91f79764d7d3fb29be5e6211965c9aad7226f4e364`。
主定理 statement_id：
`sha256:4f1ca565e074ba20cbb27329cdabe74d18ccf03e0bb3073a173576dde4a36a91`。
模块冻结 statement_id：
`sha256:380463defe87d657bbf3d29d7da3b479dcbe31cf456d33ae6096501625393669`。
新增 accepted 记录：
`965bfedcf2e373d1b4f42e7bf7fc470235950cf5e5d2dc8ac3d002656318ed5a.json`。
形式为 **deposit-uncovered**：模块已冻结，源 atom 未新增 coverage 边。
没有自写理论卷或摄入新 atom。

首次串行构建失败后，使用已盖缓存 stamp 的热树单文件 Lean 检查诊断；
错误是零根过滤归约与 CStarMatrix/Matrix 强制转换的 elaboration，
通过显式有限和及类型标注修复。`diagnostics-1/2/3.log` 中的 sorryAx
对应失败 elaboration，不能作为证明；最终 diagnostics-4 与正式 report 无此公理。
没有构建被杀或孤儿清理，没有改动两份用户点名的高内存模块。
首次 emit 的投影产生后、其尾部查询尚在运行时启动了 deposit；
在 deposit 的冻结步骤前已取得该 emit 的 exit 0，且 deposit 自身再次依次
执行 report → emit → freeze 并全部 exit 0。此重叠如实记录，不伪报命令严格串行。
随后在同一源码上用同步 subprocess 顺序执行并逐项等待
serial-lean → make lean-report → make emit → make deposit-uncovered，
四个退出码均为 0，最终哨兵 `ORDERED_GATE_CHAIN status=complete failed=0`。
日志为 attempt 的 `ordered-build.log`、`ordered-report.log`、`ordered-emit.log`、
`ordered-deposit.log`；串行构建确认无缺失模块，deposit 确认模块已冻结。
由此补齐严格串行门链的收尾证据。分支已推送至 `origin/lane/math/inoutbalance`，
未创建 PR；本次 implementation 交回 runner 作后续独立评审。

build_seconds: null（未另做计时实验）。无剩余数学子命题；
初始等距映射的保纯性没有单独形式化，主定理直接采用用户指定的最终全局纯态前提。
