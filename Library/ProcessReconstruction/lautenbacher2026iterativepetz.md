---
bibkey: lautenbacher2026iterativepetz
authors: Lea Lautenbacher, Felix Ahnefeld, Susana F. Huelga, and Martin B. Plenio
year: 2026
title: Iterative Petz Protocols for Quantum State Recovery
doi: 10.48550/arXiv.2611.32995
url: https://arxiv.org/abs/2611.32995v1
claim: "Definition 1 gives the ideal iterative Petz protocol. Theorem 2 solves the Pauli-design dephasing fidelity recurrence. Appendix B compares its Haar average numerically."
strata_touched:
  - D5/S3/Quantum/Recovery/IterativePetz/IterativePetzDephasing
  - D5/S3/Quantum/Recovery/IterativePetz/IterativePetzHaar
license: citation-only
triage: anchor
---

# Ideal iterative Petz recovery under single-axis dephasing

Definition 1 initializes the processed state at the noisy output and the
reference at the maximally mixed state. After one Petz step, the process
uses the recovered state both as its reference and as the next input to
recovery. Theorem 2 computes the mean fidelity on the six Pauli eigenstates.
Appendix B establishes axial symmetry and identifies this mean with
Simpson quadrature for the Haar mean. Figure 6 reports a numerical
asymptotic Haar deficit. [Definition 1 and Theorem 2](https://arxiv.org/html/2611.32995v1#S4) ·
[Appendix B and Figure 6](https://arxiv.org/html/2611.32995v1#A2.p9.1)

## Verified locator

[arXiv v1 abstract and bibliographic record](https://arxiv.org/abs/2611.32995v1) ·
[arXiv DOI](https://doi.org/10.48550/arXiv.2611.32995) ·
[Definition 1, Eqs. (5)–(6)](https://arxiv.org/html/2611.32995v1#S4.E6) ·
[Appendix B, numerical Haar deficit](https://arxiv.org/html/2611.32995v1#A2.p9.1)

## Pure-state limit and strict fidelity loss

Let the channel fix the diagonal and multiply the coherence by
$0<a<1$. By covariance about the noise axis, take the coherence $c$
real and nonnegative and write $z$ for the axial Bloch coordinate.
For a pure target with coordinates $(c_*,z_*)$, the first recovered
coordinates are $(a^2c_*,z_*)$. This uses the fact that dephasing is
unital and self-adjoint. The poles are fixed points and use Definition
1's stopping convention.

For any later iterate $sigma$ with $c>0$, set
$s^2=(1-z^2)/4-c^2$ and $d^2=(1-z^2)/4-a^2c^2$, with $s,d>0$.
The channel and the invertible square-root congruences preserve
positive definiteness. The trace is one by trace preservation of the
Petz map. Define $lambda=a(1-a)cs/[d^2(1+2d)]$. The update is
$$
c'=c+lambdaleft(s(1+2d)+rac{z^2(d-s)}{1+2s}
ight),qquad
z'=zleft(1-rac{4clambda(d-s)}{1+2s}
ight).
$$
For a positive definite trace-one matrix $A$ of order two,
Cayley–Hamilton gives
$sqrt A=(A+sqrt{det A}I)/sqrt{1+2sqrt{det A}}$.
With $p=(1+z)/2$ and $q=1-p$, the inverse square root of the
dephased iterate is
$left(egin{smallmatrix}q+d&-ac\-ac&p+dend{smallmatrix}
ight)/
[dsqrt{1+2d}]$. Inserting these roots in the Petz map gives the
displayed update by matrix multiplication.

The coherence $c$ increases and the axial magnitude $|z|$ decreases
whenever $z
e0$. Both have limits. The identity
$$
2c(c'-c)+z(z'-z)/2=2clambda s(1+2d)
$$
implies $s'^2le s^2(1-2a(1-a)c^2/d^2)$, so the determinant goes to
zero geometrically. Indeed $d^2le1/4$ and $c$ stays above its positive
first value. The limit has rank one. On the equator it is the target.
For $0<|z_*|<1$, let $g_a(z_*)=|z_*|-|z_2|>0$. Every iterate
from the second onward obeys $1-Fge g_a(z_*)^2/4$, since for a
pure target and an arbitrary qubit Bloch vector $r$,
$4(1-F)=|r-r_*|^2+1-|r|^2$.
The Haar law of $z_*$ is uniform on $[-1,1]$. Bounded convergence
gives a limiting mean fidelity with deficit at least
$	frac18int_{-1}^1 g_a(u)^2,du>0$ for each $a$.

## Pointwise fidelity at large depth

Write $t=4c\lambda(d-s)/(1+2s)$ for the fractional decrease in
$|z|$. Since $d\ge\sqrt{1-a^2}c$ and $c\le1/2$,
$t\le 2a(1-a)s/\sqrt{1-a^2}$. Thus $\sum_k t_k<\infty$ from
the geometric bound, and $t_k\le1/4$ gives $\prod_k(1-t_k)>0$.
For $0<|z_*|<1$, the limit has the same axial sign and
$0<|z_\infty|<|z_*|$. Its coherence exceeds $c_*$ by purity.

In the fidelity increment,
$$
\frac{F_{k+1}-F_k}{2\lambda_k}
=
c_*s_k(1+2d_k)
+\frac{d_k-s_k}{1+2s_k}\,z_k(c_*z_k-z_*c_k),
$$
the first update from $(a^2c_*,z_*)$ gives a positive right-hand
side. At large $k$, the first term tends to zero and the second tends
to $d_\infty z_\infty(c_*z_\infty-z_*c_\infty)<0$.
The fidelity therefore improves at first and decreases strictly at
sufficiently large depths for each such target. The integrated Haar
curve's eventual monotonicity requires a separate estimate.

The proof concerns the ideal recurrence of Definition 1.
The related tomography analyses of Murk et al. and Sidajaya et al.
use a fixed classical observation as the processed evidence for their
batch update. [Murk et al.](https://arxiv.org/abs/2606.23777v2) ·
[Sidajaya et al.](https://arxiv.org/abs/2608.21309v1)
