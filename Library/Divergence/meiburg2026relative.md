---
bibkey: meiburg2026relative
authors: Alex Meiburg
year: 2026
title: Uniform power-slope control for singular relative-entropy limits
doi: null
url: https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean
claim: The two-sided power difference quotient converges uniformly to x log x on every bounded nonnegative spectral interval, including zero.
strata_touched:
  - D5/S3/Quantum/Divergence/RenyiDivergence/UniformPowerSlope
license: Apache-2.0
triage: anchor
---

# Uniform power slopes at a singular endpoint

## Verified locator

The source is `QuantumInfo/Entropy/Relative.lean`, declaration
`rpow_slope_tendsto_uniformly`, at Physlib revision
`b9043cc548ef6d63a28454cf3a57fb12a0c2e142`:
https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean#L877

The source header credits Alex Meiburg, copyright 2026, and Apache 2.0.
The selected proof retains that header and attribution. The full supplier
license is `docs/reports/inoutbalance/physlib-LICENSE.txt`; the supplier root
has no NOTICE file. This selected proof does not include the supplier's
MIT-marked `HermitianMat/LiebConcavity.lean` material.

The estimate splits the spectral interval into a common neighborhood of
zero and a compact positive interval. Exponential domination controls both
signs of the exponent perturbation at zero; a uniform quadratic remainder
controls the compact interval. It imposes no positive lower spectral bound.
The zero term uses positive exponents near one and the convention
`0 * log 0 = 0`.

## Uniform convergence statement and proof

**引理 1（有界非负谱上的一致幂差商）。** 任取实数 $K$。对每个 $\varepsilon>0$，存在 $\delta>0$，使得所有满足 $0<|h|<\delta$ 的实数 $h$ 以及所有 $x\in[0,K]$ 都满足
$$
\left|\frac{x^{1+h}-x}{h}-x\log x\right|<\varepsilon.
$$
这里使用自然对数，$0\log0=0$；$K<0$ 时区间为空。差商从正负两侧趋近，包含 $x=0$，不要求非零谱或正下界。

**证明。** 对 $0<x$ 写 $x^{1+h}=x\exp(h\log x)$。指数余项给出差商的界
$$
\left|\frac{x^{1+h}-x}{h}\right|
\le x(|\log x|+1)\exp\bigl(|h|(|\log x|+1)\bigr).
$$
当 $|h|<1/2$ 时，右端由 $x(|\log x|+1)\exp((|\log x|+1)/2)$ 控制；令 $y=-\log x$，它化为常数乘 $(y+1)e^{-y/2}$，在 $x\downarrow0$ 时趋于零。$x\log x$ 同样趋于零。故靠近零的共同小区间内两项均可一致控制。在剩余紧区间 $[a,K]$（$a>0$）上，指数的二阶余项给出
$$
\left|\frac{x^{1+h}-x}{h}-x\log x\right|
\le |h|x(\log x)^2\exp(|h||\log x|),
$$
其除 $|h|$ 之外的因子在该紧区间上一致有界。选择共同的 $\delta$ 即得结论；$x=0$ 且 $|h|<1/2$ 时 $1+h>0$，两项均为零。该论证取自 Alex Meiburg 的 [Physlib 原始证明](https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean)，声明 `rpow_slope_tendsto_uniformly`。

## Mathematical scope

The estimate concerns real scalar power difference quotients on bounded
nonnegative intervals. It has no state dimension hypothesis. It does not
establish the variable-base matrix trace limit, operator Jensen, Lieb
concavity, data processing, quantum Pinsker, or the complete thermal
recovery theorem. The statement and proof are attributed to the immutable
Physlib source cited above; no mathematical originality is claimed.
