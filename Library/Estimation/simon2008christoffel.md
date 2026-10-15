---
bibkey: simon2008christoffel
authors: Barry Simon
year: 2008
title: "The Christoffel-Darboux Kernel"
doi: null
url: https://arxiv.org/abs/0806.1528v1
claim: "The Christoffel variational principle bounds a point mass using finite moments; its interior kernel estimate also bounds polynomial point evaluation by a local L2 norm."
strata_touched: []
license: citation-only
triage: anchor
---

# Endpoint mass from finite moment observations

Source: https://arxiv.org/abs/0806.1528v1. Theorem 2.1, PDF p. 5,
identifies the inverse Gram moment matrix with the polynomial
reproducing-kernel coefficient matrix. Theorem 9.2, PDF p. 15,
equation (9.6), gives the minimum of $\int|P|^2d\mu$ under
$P(x)=1$, $\deg P\le d$, as $1/K_d(x,x)$.
Theorem 9.7, PDF p. 17, equation (9.21), gives
$K_d(x,x)\to\mu(\{x\})^{-1}$ for compact real support, with infinity
when the atom has mass zero.

The consumer is
[LocalClock, §十四, 定理27](../../docs/develop/theory/AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md):
$x=1$, support $[0,1]$, $H_d=[c_{i+j}]$ and
$v=(1,\ldots,1)^T$. For $H_d$ positive definite this yields
$B_d=(v^TH_d^{-1}v)^{-1}$. Singular matrices use the original
constrained quadratic minimum; no inverse is asserted. The consumer
also gives the elementary endpoint squeeze using $P(\lambda)=\lambda^d$,
so its finite-support cases do not require an infinite orthogonal
polynomial family. This is a classical estimation certificate, not a
new moment theorem or a finite-sample guarantee.


## Interior polynomial evaluation

The same primary version, Theorem 9.2, equation (9.6), printed p.15,
and Theorem 9.6, equation (9.20), printed p.16, also supply the
point-evaluation input used in the
[fixed local Möbius-moment application](../Analytic/verjovsky2026mobiussmoothing.md#classical-polynomial-evaluation-sharpens-the-fixed-moment-input).
These selected statements and their proofs were inspected; no whole-paper
or Lean verification is asserted.

For fixed $c>0$, take the probability measure $dy/(2c)$ on $[-c,c]$.
Its density is bounded below on a neighborhood of the interior point
zero. Theorem 9.6 with its imaginary displacement equal to zero gives
$K_k(0,0)\ll_c k+1$. Theorem 9.2 consequently supplies, for every
complex polynomial $P$ of degree at most $k$,
$$
|P(0)|\ll_c\sqrt{k+1}
\left(\frac1{2c}\int_{-c}^c|P(y)|^2\,dy\right)^{1/2}.
$$
The constant is independent of the degree and polynomial. The degree-zero
case follows from the constant polynomial norm. This is an application
of the cited classical kernel bounds, not a new polynomial inequality.
It supplies no bound for deterministic Möbius moments by itself.
