---
bibkey: blore2026partialtrace
authors: Zayn Blore
year: 2026
title: Partial trace and spectral von Neumann entropy in CsdLean4
doi: null
url: https://github.com/zblore/csd-lean4/tree/13eda16971c66de4bc9f550e418dd4fdf59a5121/CsdLean4/Mathlib
claim: Partial traces preserve positivity and trace; spectral entropy is additive on product density operators.
strata_touched:
  - D5/S3/Quantum/Information/PartialTraceMutualInformation
license: Apache-2.0
triage: anchor
---

# 偏迹与乘积态熵

## Verified locator

已读取的固定版本源码定位为：
https://github.com/zblore/csd-lean4/tree/13eda16971c66de4bc9f550e418dd4fdf59a5121/CsdLean4/Mathlib

LinearAlgebra/Matrix/PartialTrace.lean 的 Matrix.PosSemidef.traceLeft、
Matrix.PosSemidef.traceRight、Matrix.trace_traceLeft、Matrix.trace_traceRight
给出偏迹的半正定性与保迹。QuantumInfo/Entropy.lean 的
QuantumInfo.spectral_sum_kronecker 与 QuantumInfo.vonNeumannEntropy_kronecker
给出任意密度算子乘积的谱熵可加性；QuantumInfo/TraceDistance.lean 的
QuantumInfo.re_trace_cfc 把谱求和接到函数演算的迹。

本仓移植上述证明到已有偏迹接口，使用 Mathlib 的 Real.negMulLog_mul，
并通过 CStarMatrix.ofMatrixStarAlgEquiv 将谱熵接到已有的 CFC.log 迹定义。
源码版权声明与 Apache-2.0 全文保留于正式模块及
docs/reports/qmutualinfo/csd-lean4-LICENSE.txt。
