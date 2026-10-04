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
  - D5/S3/Quantum/Divergence/CanonicalChannelDPI
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

## Canonical channel relative entropy

Let a,b be finite nonempty complex matrix carriers, Phi a completely positive
trace-preserving linear map, and rho,sigma positive semidefinite matrices of
trace one. All logarithms are natural. Define
$$
D(\rho\|\sigma)=
\begin{cases}
\operatorname{Re}\operatorname{Tr}\rho(\log\rho-\log\sigma),
 &\ker\sigma\subseteq\ker\rho,\\
+\infty,&\text{otherwise}.
\end{cases}
$$
The functional-calculus logarithm is totalized at zero; the infinite branch is
specified by the actual vector kernels. For every such channel and state pair,
$$
D(\Phi(\rho)\|\Phi(\sigma))\le D(\rho\|\sigma).
$$
This includes dimension one and singular noncommuting states.

The support contraction argument follows Petz, *Monotonicity of quantum
relative entropy revisited*, §3, equations (3)–(4),
https://arxiv.org/abs/quant-ph/0209053, and Hiai–Mosonyi–Petz–Bény,
*Quantum f-divergences and error correction*, version 6, §4, Lemmas 4.1–4.2,
https://arxiv.org/abs/1008.2529v6. The latter version corrects an earlier
continuity proposition. This argument uses only a finite scalar logarithm limit.
These are known results; the coordinates below express their argument on
finite matrices.

**Argument.** Choose one Kraus family implementing the given channel:
$$
\Phi(X)=\sum_c K_cXK_c^*,\qquad \sum_c K_c^*K_c=I_a.
$$
For positive semidefinite X,
$$
\ker\Phi(X)=\{y:\ \forall c,\ XK_c^*y=0\}.
$$
Indeed its quadratic form is the finite sum of nonnegative numbers
$\sum_c\|X^{1/2}K_c^*y\|^2$. It vanishes precisely when every term vanishes.
The same family therefore transfers input support inclusion to output support
inclusion. If input support fails, the inequality has right side $+\infty$.

Assume input support. Write $\tau=\Phi(\rho)$, $\omega=\Phi(\sigma)$.
Use positive spectral index sets I,J,K,L and eigenvectors in the original
ambient carriers:
$$
\rho=\sum_{i\in I}r_i u_i u_i^*,\quad
\sigma=\sum_{j\in J}s_j v_j v_j^*,\quad
\tau=\sum_{k\in K}p_k z_k z_k^*,\quad
\omega=\sum_{\ell\in L}q_\ell w_\ell w_\ell^* .
$$
All four eigenvalue families are strictly positive. The input eigenvectors
belong to $\mathbb C^a$, and the output eigenvectors belong to $\mathbb C^b$.
Support gives $P_\sigma u_i=u_i$ and $P_\omega z_k=z_k$.
On $S=J\times I$, $T=L\times K$, put
$$
A_{ji,ji}=s_j/r_i,\quad B_{\ell k,\ell k}=q_\ell/p_k,\quad
\xi_{ji}=\sqrt{r_i}\,v_j^*u_i,\quad
\eta_{\ell k}=\sqrt{p_k}\,w_\ell^*z_k .
$$
These diagonal matrices are strictly positive; both vectors have norm one.
Finite spectral expansion, including the vanished zero-support weights, gives
$$
D(\rho\|\sigma)=-\langle\xi,\log A\,\xi\rangle,\quad
D(\tau\|\omega)=-\langle\eta,\log B\,\eta\rangle.
$$

Define the actual rectangular amplitude matrix
$$
V_{ji,\ell k}=\frac{\sqrt{r_i}}{\sqrt{p_k}}
 \sum_c(v_j^*K_c^*w_\ell)(z_k^*K_cu_i).
$$
The Kraus sum precedes every squared modulus. Write
$\Psi(Y)=\sum_cK_c^*YK_c$,
$\widehat y=\sum_{\ell,k}y_{\ell k}w_\ell z_k^*$, and
$Y=\widehat y\,\tau_+^{-1/2}$. Finite expansion gives
$\widehat{Vy}=P_\sigma\Psi(Y)\rho^{1/2}$.
Stack the same Kraus operators as an isometry $W_0$.
For the block amplification $\widetilde Y$,
$$
\Psi(Y^*Y)-\Psi(Y)^*\Psi(Y)
 =W_0^*\widetilde Y^*(I-W_0W_0^*)\widetilde YW_0\ge0.
$$
Replacing Y by its adjoint supplies the other Schwarz orientation.
Trace cyclicity and the Kraus pairing give
$$
\begin{aligned}
\|Vy\|^2
&\le\operatorname{Tr}\rho\,\Psi(Y)^*\Psi(Y)
\le\operatorname{Tr}\tau\,Y^*Y=\|y\|^2,\\
\langle Vy,AVy\rangle
&=\operatorname{Tr}\sigma\,\Psi(Y)P_\rho\Psi(Y)^*
\le\operatorname{Tr}\omega\,YY^*=\langle y,By\rangle .
\end{aligned}
$$
Thus $V^*V\le I_T$ and $V^*AV\le B$.
The kernel identity gives $P_\tau K_c\rho^{1/2}=K_c\rho^{1/2}$;
Kraus normalization consequently gives $V\eta=\xi$.

Set $G=I_T-V^*V$. It satisfies $0\le G\le I_T$.
Norm equality gives $\langle\eta,G\eta\rangle=0$, hence
$G\eta=G^{1/2}\eta=0$.
The matrix $W=[V;G^{1/2}]$ is an isometry. For every $\lambda>0$,
let $D_\lambda=A\oplus\lambda I_T$. Isometric logarithm compression,
obtained from operator concavity by reflection across the range of W and
the functional-calculus range identity, gives
$$
W^*(\log D_\lambda)W\le\log(W^*D_\lambda W)
\le\log(B+\lambda I_T).
$$
The second step uses $W^*D_\lambda W=V^*AV+\lambda G\le B+\lambda I_T$
and operator monotonicity on strictly positive matrices.
Evaluation on eta annihilates the defect term $(\log\lambda)G$.
The right side is the finite sum
$\sum_{\ell,k}|\eta_{\ell k}|^2\log(q_\ell/p_k+\lambda)$.
Scalar continuity as lambda decreases to zero and the trace-log identities
prove the supported inequality and complete the support split. No ambient
faithfulness, unital Schrodinger channel, or logarithm continuity at a zero
eigenvalue is used.
