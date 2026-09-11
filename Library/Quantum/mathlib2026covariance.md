---
bibkey: mathlib2026covariance
authors: Mathlib contributors
year: 2026
title: Weighted matrix inner products and bounded variances in Mathlib
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Matrix/Order.lean
claim: Positive semidefinite matrices induce a semi-inner product; its Cauchy-Schwarz bound applies to centered observables.
strata_touched:
  - D5/S3/Quantum/Information/CovarianceSumBound
license: Apache-2.0
triage: anchor
---

# 密度态协方差的上游接口

## Verified locator

已读取的固定版本源码定位为：
https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Matrix/Order.lean

Matrix.toMatrixSeminormedAddCommGroup 与 Matrix.toMatrixInnerProductSpace
实现由正半定 M 诱导的配对 tr(y M xᴴ)，不要求 M 可逆。
Mathlib/Analysis/InnerProductSpace/Basic.lean 的 norm_inner_le_norm
提供 Cauchy–Schwarz；本模块证明中心化后其实部等于对称化协方差。

Mathlib/Probability/Moments/Variance.lean 的 variance_le_sq_of_bounded
给出经典 Popoviciu 半宽界。本模块使用同版连续函数演算
cfc_le_algebraMap_iff 将谱上的 (t−c)²≤Δ² 输送到矩阵序，再用
正的密度态期望和均值偏移平方得到量子态上的同一半宽界。
稀疏有限和的组合由本仓完成；没有声称这些上游文件已经定义本仓的协方差。
