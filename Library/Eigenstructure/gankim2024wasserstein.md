---
bibkey: gankim2024wasserstein
authors: Luyining Gan; Sejong Kim
year: 2024
title: Weak log-majorization between the geometric and Wasserstein means
doi: 10.48550/arXiv.2301.07934
url: https://arxiv.org/abs/2301.07934
claim: Conjecture 5.7 proposes weak log-majorization monotonicity and convergence of the power-transformed Wasserstein mean as its exponent decreases to zero.
strata_touched:
  - D5/S3/Quantum/Matrix/WassersteinMean
  - D5/S3/Quantum/Matrix/GanKimConjectureRefutation
license: citation-only
triage: anchor
---

# Weak log-majorization between the geometric and Wasserstein means

## Locator

- Source: https://arxiv.org/abs/2301.07934 ; specified version arXiv:2301.07934v4.
- arXiv DOI: https://doi.org/10.48550/arXiv.2301.07934.
- Location: arXiv:2301.07934v4, §5, Conjecture 5.7.
- Supplied journal locator: *Journal of Mathematical Analysis and Applications* 530(2) (2024), 127711. Journal DOI: ASSUMED-UNVERIFIED; no primary journal text is available locally for confirmation.

## Source statement and definitions

> Conjecture 5.7. Let A, B ∈ Pm and t ∈ (0, 1). Then (A^p ⋄t B^p)^{1/p} ց≺w log exp((1 − t) log A + t log B) as p ց 0.

The supplied definition is:

> A ⋄t B := (1 − t)² A + t² B + t(1 − t)[A(A^{−1} #B) + (A^{−1} #B)A]

Here $\mathbb P_m$ consists of complex Hermitian positive definite matrices and

$$
A\#B=A^{1/2}(A^{-1/2}BA^{-1/2})^{1/2}A^{1/2}.
$$

For decreasingly ordered eigenvalues, weak log-majorization means

$$
X\prec_{w\log}Y\quad\Longleftrightarrow\quad
\prod_{i=1}^k\lambda_i(X)\le\prod_{i=1}^k\lambda_i(Y)
\quad(1\le k\le m).
$$

Write $F_t(p)=(A^p\diamond_tB^p)^{1/p}$. The decreasing arrow is rendered as the conjunction of $F_t(p)\prec_{w\log}F_t(q)$ for every $0<p<q$, and the right-hand limit of $F_t(p)$ at zero being $\exp((1-t)\log A+t\log B)$. Real powers, logarithms and exponentials use continuous functional calculus. The zero-length eigenvalue product, when included, is $1\le1$ and adds no condition.

## Counterexample

Set

$$
A=\begin{pmatrix}81&0\\0&1\end{pmatrix},\qquad
B=\begin{pmatrix}41&40\\40&41\end{pmatrix},\qquad
P=A^{1/2}=\begin{pmatrix}9&0\\0&1\end{pmatrix},\qquad
Q=B^{1/2}=\begin{pmatrix}5&4\\4&5\end{pmatrix}.
$$

All four matrices are positive definite. The Riccati solutions are

$$
T_1=P^{-1}\#Q=\frac1{\sqrt{17}}\begin{pmatrix}3&2\\2&7\end{pmatrix},\qquad
T_2=A^{-1}\#B=\frac1{\sqrt{881}}\begin{pmatrix}21&20\\20&61\end{pmatrix}.
$$

Indeed $T_1PT_1=Q$ and $T_2AT_2=B$, and positive definiteness identifies the solutions uniquely. If $X,Y\in\mathbb P_2$ have equal determinant $d$ and $T=X^{-1}\#Y$, then $\det T=1$ and

$$
\det(X\diamond_tY)=d[1+t(1-t)(\operatorname{tr}T-2)]^2.
$$

Put $h=t(1-t)$, $u=10/\sqrt{17}-2$ and $v=82/\sqrt{881}-2$. The exact inequalities $u>2/5$ and $0<v<4/5$ give $2u>v>0$. Consequently, for every $0<t<1$,

$$
(1+hu)^2-(1+hv)=h(2u-v)+h^2u^2>0,
$$

and therefore

$$
\det F_t(1/2)=81(1+hu)^4>81(1+hv)^2=\det F_t(1).
$$

The full eigenvalue product in weak log-majorization would require the opposite determinant inequality. Thus the monotonicity assertion fails for every internal weight, for the same two matrices.

## Scope and literature boundary

The definitions and the conjecture are attributed to Gan and Kim. The explicit matrices, Riccati calculations and determinant comparison are repository derivations. Theorem 5.6 retains its additional hypothesis (5.15) and is unaffected by a refutation of the unconditional conjecture. The exact text of (5.15), and a direct verification that these matrices violate it, are ASSUMED-UNVERIFIED because the primary text of that condition is unavailable locally. The determinant obstruction alone does not refute convergence without monotonicity.

The literature check covered "2301.07934" with conjecture or counterexample, Wasserstein mean with log-Euclidean and weak log-majorization, and the title. Related work checked: Bhatia–Jain–Lim 2019; arXiv:1904.09385; arXiv:2307.15315; arXiv:2501.00287, which cites Gan–Kim. None resolves Conjecture 5.7. Citation indexes were not exhaustively checked; no settlement found within that scope.

Absence of later settlements and worldwide priority are not established. This citation-only note incorporates no external source software.
