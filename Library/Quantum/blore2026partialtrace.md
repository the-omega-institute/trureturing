---
bibkey: blore2026partialtrace
authors: Zayn Blore
year: 2026
title: Partial trace, spectral entropy and general Lie-Trotter products in CsdLean4
doi: null
url: https://github.com/zblore/csd-lean4
claim: Partial traces preserve positivity and trace; spectral entropy is additive on product density operators; the general real Banach-algebra Lie-Trotter formula follows from exponential-series and growth-controlled telescoping estimates.
strata_touched:
  - D5/S3/Quantum/Information/PartialTraceMutualInformation
  - D5/S3/Quantum/Analysis/TrotterProduct
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

## General Lie-Trotter products

The directly inspected immutable Lean proof source is
https://github.com/zblore/csd-lean4/tree/ff2d274f684df1c500c9f4dae8541c57f236ca6a.
The selected file is CsdLean4/Mathlib/Analysis/NormedSpace/TrotterGeneral.lean,
SHA-256 5f659c39f0695fe511a952c2b7a7fd97b3758827b5dc22aa88ca4b564a8476b9.
This selection is independent of the partial-trace and spectral-entropy source
revision recorded above.

The general Trotter theorem assumes a complete real normed algebra with norm-one
identity and permits arbitrary noncommuting inputs. The nth power is taken of
the product of the two scaled exponentials. For every integer n at least one,
the proof bounds its norm error from exp(X+Y) by n inverse times
s squared times (3+s) times exp(2s), where s is the sum of the two input norms.
This estimate remains internal to the convergence proof.

The source uses Lean 4.34.0 and Mathlib 5ed2965256430c3649e86755f9576b54eca72435.
The host uses Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
The selected host-compatible source donor is repository commit
fded3060402bfb78dc53c78d011ffe19332e6b73. Modifications select only the live
Trotter declarations and adapt imports, visibility and compatibility. The
repeated-exponential identity is supplied directly by Mathlib's exp_nsmul
after restricting scalars to the rationals; it adds no algebra hypothesis.
The formal module retains Zayn Blore's copyright, authorship, Apache-2.0
notice and modification notice. The reused complete license is
docs/reports/qmutualinfo/csd-lean4-LICENSE.txt, 11357 bytes, SHA-256
c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4.
The immutable source tree has no NOTICE file. Retire this transplant only when
the repository actually adopts a Mathlib pin supplying equivalent complete
statements and migrates the actual consumers.

This is an attributed source selection of known mathematics. No original-proof
or mathematical-novelty credit is claimed. Classical publisher fulltexts are
not the inspected Lean proof source recorded here.
