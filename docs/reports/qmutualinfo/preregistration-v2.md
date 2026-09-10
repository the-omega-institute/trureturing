# 偏迹与互信息修复：预登记 v2

v1 的目标与验收不变；准入依据在证明实施前修订。

proof_shape: bind-only
admission_basis: rule-11-upstream-wrapper
escape_witness: none（精确第三方命中，不再申报本仓原创见证）

精确命中：zblore/csd-lean4，rev 13eda16971c66de4bc9f550e418dd4fdf59a5121，
CsdLean4/Mathlib/LinearAlgebra/Matrix/PartialTrace.lean 中
Matrix.PosSemidef.traceLeft、Matrix.PosSemidef.traceRight、
Matrix.trace_traceLeft、Matrix.trace_traceRight。
源文件版权 Zayn Blore，Apache-2.0；根目录树有 LICENSE，无 NOTICE。
实测上游 toolchain=v4.33.0、mathlib=db584cd6d46c92f209a44c0f1c829460d327499d，
与本仓相同。A17 公共来源/不可变版本/许可的 automatic admission 谓词仍 open，
不引入未经该契约准入的新 Lake 依赖；采用 A17.2 的带来源移植形，保留版权及许可全文。
本仓钉版 Mathlib 出现等价偏迹声明时，移除移植证明并直接引用。

包装的具体 API 义务：用户要求在既有 partialTraceLeft/partialTraceRight 上构造
DensityState 边缘，用于仅接受一个联合态的 quantumMutualInformation。
保留既有偏迹接口，移植上游证明到这些接口，不创建第二套偏迹定义。
伴随边方向：marginalLeft → partialTraceLeft_posSemidef / trace_partialTraceLeft；
marginalRight → partialTraceRight_posSemidef / trace_partialTraceRight；
quantumMutualInformation → 两个 marginal。

utility: none；理由及非平凡第三目标仍按 v1。

实施前补充精确命中：同一 rev 的 QuantumInfo/Entropy.lean 提供
spectral_sum_eq_of_charpoly_prod、spectral_sum_kronecker、
vonNeumannEntropy_kronecker；TraceDistance.lean 提供 re_trace_cfc。
这些亦采取保留来源的最小移植。Mathlib 精确命中 Real.negMulLog_mul，直接引用，
不移植上游同名自证辅助引理。把谱熵与本仓 CStarMatrix 上的 CFC.log 迹表达式对齐，
再由真实偏迹边缘推出 quantumMutualInformation (productState rho sigma) = 0。
全部仍按 rule-11-upstream-wrapper，不以移植内容申报原创逃逸。
