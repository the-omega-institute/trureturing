---
slug: gan-kim-2024-wasserstein-weak-log-majorization
bibkey: gankim2024wasserstein
doi: 10.48550/arXiv.2301.07934
url: https://arxiv.org/abs/2301.07934
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/GanKimConjectureRefutation.result
---

# Gan–Kim: weak log-majorization monotonicity of Wasserstein power means

## Problem

Luyining Gan and Sejong Kim, *Weak log-majorization between the geometric and Wasserstein means*, arXiv:2301.07934v4, §5, Conjecture 5.7. See [gankim2024wasserstein](../Library/Eigenstructure/gankim2024wasserstein.md).

> Conjecture 5.7. Let A, B ∈ Pm and t ∈ (0, 1). Then (A^p ⋄t B^p)^{1/p} ց≺w log exp((1 − t) log A + t log B) as p ց 0.

> A ⋄t B := (1 − t)² A + t² B + t(1 − t)[A(A^{−1} #B) + (A^{−1} #B)A]

Here $A\#B=A^{1/2}(A^{-1/2}BA^{-1/2})^{1/2}A^{1/2}$ and $\mathbb P_m$ is the cone of complex Hermitian positive definite matrices. Weak log-majorization compares every initial product of decreasingly sorted eigenvalues, including the product of all $m$ eigenvalues.

For $F_t(p)=(A^p\diamond_tB^p)^{1/p}$, the decreasing arrow is the conjunction of the comparisons $F_t(p)\prec_{w\log}F_t(q)$ for all real $0<p<q$ and the right-hand limit $F_t(p)\to\exp((1-t)\log A+t\log B)$ as $p\downarrow0$. The formal statement includes both assertions, every finite dimension, all complex positive definite inputs and every real $0<t<1$.

## Motivation

The conjecture removes the extra hypothesis (5.15) from the paper's Theorem 5.6 and proposes an unconditional power-parameter monotonicity law for the Wasserstein mean. The assertion and proposed counterexample are identified in [issue #19050](https://github.com/the-omega-institute/trureturing/issues/19050).

## Gap

The full eigenvalue product can increase when the power parameter decreases. Equal spectra of the two input matrices do not prevent this determinant obstruction.

## Route

Take

$$
A=\begin{pmatrix}81&0\\0&1\end{pmatrix},\quad
B=\begin{pmatrix}41&40\\40&41\end{pmatrix},\quad
P=\begin{pmatrix}9&0\\0&1\end{pmatrix},\quad
Q=\begin{pmatrix}5&4\\4&5\end{pmatrix}.
$$

Then $P=A^{1/2}$, $Q=B^{1/2}$, and the positive definite solutions of $T_1PT_1=Q$ and $T_2AT_2=B$ are

$$
T_1=\frac1{\sqrt{17}}\begin{pmatrix}3&2\\2&7\end{pmatrix},\qquad
T_2=\frac1{\sqrt{881}}\begin{pmatrix}21&20\\20&61\end{pmatrix}.
$$

Riccati uniqueness identifies them with the required inverse geometric means. With $h=t(1-t)$, $u=10/\sqrt{17}-2$ and $v=82/\sqrt{881}-2$, the determinant identities are

$$
\det F_t(1/2)=81(1+hu)^4,\qquad
\det F_t(1)=81(1+hv)^2.
$$

Exact squared comparisons give $u>2/5$ and $0<v<4/5$. For $0<t<1$, $h>0$, so

$$
(1+hu)^2-(1+hv)=h(2u-v)+h^2u^2>0.
$$

Squaring the positive sides proves $\det F_t(1/2)>\det F_t(1)$.

## Falsifier

The same two positive definite integer matrices violate the conjectured comparison at $p=1/2$ and $q=1$ for every $t\in(0,1)$. The determinant is the product at the full prefix $k=2$, so a strict reverse determinant inequality refutes weak log-majorization itself.

## Evidence

`D5/S3/Quantum/Matrix/GanKimConjectureRefutation.result : ¬ conjecture` targets the full quantified conjecture, including its limit conjunct. The certificate belongs to that module. `D5/S3/Quantum/Matrix/WassersteinMean.weakLogMajorization_det_le` supplies the implication from the eigenvalue-product comparison to the determinant inequality. The counterexample refutes the monotonicity conjunct; the proof does not use a failure of the limit conjunct.

## Triage

**PROVED — Refutation of Conjecture 5.7, for every $0<t<1$.** For $A=\operatorname{diag}(81,1)$ and $B=\left(\begin{smallmatrix}41&40\\40&41\end{smallmatrix}\right)$, the comparison from $p=1/2$ to $q=1$ fails at the product of both eigenvalues.

**OPEN — formal non-implication for Theorem 5.6 under (5.15).** The unconditional conjecture and the conditional theorem are distinct assertions. Direct violation of the literal hypothesis (5.15) by these matrices is ASSUMED-UNVERIFIED here: its primary-source text is unavailable locally, and no Lean theorem about that condition is asserted.

**OPEN — convergence without monotonicity.** The determinant counterexample does not decide the limit of $F_t(p)$ as $p\downarrow0$. No global claim that this convergence is unresolved in the literature is made.

## ASSUMED-UNVERIFIED

The exact condition (5.15), its failure for the displayed pair, and the journal DOI have not been confirmed against primary text. Absence of subsequent settlements and worldwide priority are not established. Convergence alone is not proved or refuted by this module.
