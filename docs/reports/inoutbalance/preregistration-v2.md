# 预登记 v2：精确上游命中后降级

v1 的目标、实际三体约化态约束与三态验收保持不变。

proof_shape: `bind-only`
admission_basis: `rule-11-upstream-wrapper`
escape_witness: `none`

精确命中 physlib revision `889c09c66fb5f3c4a27182a43cafbed9e00b9d0a`，
`QuantumInfo/Entropy/VonNeumann.lean` 的 `Sᵥₙ_of_partial_eq`、
`Sᵥₙ_pure_complement` 及其非零特征根辅助证明。
其版权为 Alex Meiburg，Apache-2.0；根树有 LICENSE，无 NOTICE，
许可全文保存为 `physlib-LICENSE.txt`。本仓 A17 的直接依赖准入谓词仍 open，
采用 A17.2 的带来源移植；不引入新 Lake 依赖。
本仓钉版 mathlib 出现等价声明时应退役移植，改为直接引用。

包装必要性由源 atom 的两条明文等式 `S(AR)=S(B)`、`S(AB)=S(R)` 给出。
上游使用 MState/Ket 与谱熵，本仓要求 DensityState/CStarMatrix 与迹熵，
因此须将上游证明连接到既有偏迹与熵定义。前置模块的定义和公开定理直接 import。
具名消费者仍是 `InputInformationBalance.input_information_balance`。
三体重分组、偏迹一致性、谱熵与迹熵对齐均计为 API 工作，
不以移植证明或算术收尾申报本仓原创见证。

utility: `none`；所有声明量化任意有限载体、向量或密度态，
没有四类计算性新内容。数值探针只报告实测，不冻结为实例。
