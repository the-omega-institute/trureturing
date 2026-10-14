---
bibkey: sang2026seveneighths
authors: Hejian Sang
year: 2026
title: "Refining the 7/8 zero-free half-plane for Hecke and Dirichlet L-functions"
doi: null
url: https://arxiv.org/abs/2610.15291v1
claim: "Assuming the analytic inputs of the OpenAI 7/8 result, the same finite-order Hecke family over Q(sqrt(-3)) and its Dirichlet transfer have zero-free boundary 8748867/10000000 = 0.8748867; this is an auxiliary zero-free input, not a Robin or Riemann-hypothesis proof."
strata_touched: []
license: citation-only
triage: anchor
---

# Refining the 7/8 zero-free half-plane

The source is [arXiv:2610.15291v1](https://arxiv.org/pdf/2610.15291v1), submitted 11 October 2026. It is a preprint; the argument is recorded here as a literature interface and has not been independently formalized or audited in this repository.

## The stated improvement

Hejian Sang assumes the analytic inputs used by the recent uniform $7/8$ zero-free result for finite-order Hecke $L$-functions over

$$
F=\mathbb Q(\sqrt{-3})
$$

and its transfer to Dirichlet $L$-functions. Under those inputs, the paper replaces the boundary $7/8=0.875$ by

$$
B_{\mathrm{Sang}}=\frac{8748867}{10000000}=0.8748867.
$$

The abstract attributes the gain to a relaxed direct estimate and an amplified first moment of the reflected numerator, using the existing fourth-moment estimate; it does not claim a new critical-line theorem.

Numerically, the extra room relative to $7/8$ is

$$
\frac78-B_{\mathrm{Sang}}=0.0001133.
$$

This is below the Liu v2 boundary already recorded in [the Liu source card](../Analytic/liu2026quasirh.md),

$$
B_{\mathrm{Liu,v2}}=0.874957019420098946\ldots,
$$

by approximately $0.000070319420098946$.

## Boundary for the FIB--Robin route

This source supplies a sharper conditional zero-free parameter for the same type of auxiliary $L$-function family. It does not provide zeros on $\Re s=1/2$, square-root cancellation for the ordinary Möbius function, or a pointwise signed estimate for all prime-power terms in

$$
\frac{\sigma(N)}N-e^\gamma\log\log N.
$$

Consequently, $B_{\mathrm{Sang}}$ cannot be substituted for the fixed $7/8$ parameter in an existing FIB packet without transporting the full parameter contract: lengths, moment ranges, contour bounds, and endpoint inequalities must all be rechecked together. Even after that transport, the same-candidate joint Robin budget and the FIB-address-to-divisor-sum map remain open. This card records a new auxiliary input and its exact failure boundary so that the project does not repeat the already-covered $7/8$, Liu, or Robin derivations.
