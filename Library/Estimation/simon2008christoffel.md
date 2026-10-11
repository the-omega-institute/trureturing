---
bibkey: simon2008christoffel
authors: Barry Simon
year: 2008
title: "The Christoffel-Darboux Kernel"
doi: null
url: https://arxiv.org/abs/0806.1528v1
claim: "The Christoffel variational principle bounds a point mass using finite moments; for compact real support its limit recovers the point mass."
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
