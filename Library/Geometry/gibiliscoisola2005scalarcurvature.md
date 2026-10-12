---
bibkey: gibiliscoisola2005scalarcurvature
authors: Paolo Gibilisco; Tommaso Isola
year: 2005
title: "On the monotonicity of scalar curvature in classical and quantum information geometry"
doi: 10.1063/1.1834693
url: https://arxiv.org/abs/math-ph/0407007v2
claim: "Conjecture 4.1 asks whether the scalar curvature of the logarithmic alpha-geometry is Schur-increasing on the positive simplex; this note records the p = infinity endpoint."
strata_touched:
  - D5/S3/Geometry/AlphaGeometry/MajorizationTransfer
  - D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality
  - D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing
  - D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone
license: citation-only
triage: anchor
---

# Gibilisco--Isola scalar curvature

The paper uses the positive simplex \(\mathcal P^1_n\), whose coordinates are positive and sum to one. Majorization orders vectors by being more mixed; a Schur-increasing function increases along that order, and a strictly Schur-increasing function increases unless the vectors differ only by a permutation.

Definition 2.1 (printed p. 3) defines

$$
\mathcal P^1_n:=\{\rho\in\mathbb R^n\mid\sum_i\rho_i=1,\ \rho_i>0\}.
$$

Definition 2.3 (printed p. 3): “$x$ is more mixed (more chaotic,...) than $y$ (denoted by $x\succ y$) if and only if”

$$
x^\downarrow_1+\cdots+x^\downarrow_k\leq y^\downarrow_1+\cdots+y^\downarrow_k\quad(k<n),\qquad
x^\downarrow_1+\cdots+x^\downarrow_n=y^\downarrow_1+\cdots+y^\downarrow_n.
$$

Definition 2.4 (printed p. 4): “A real-valued function $f$ defined on a set $\mathcal A\subset\mathbb R^n$ is said to be Schur-increasing on $\mathcal A$ if” $x\succ y\Rightarrow f(x)\geq f(y)$. “If in addition $f(x)>f(y)$ whenever $x\succ y$ but $x$ is not a permutation of $y$ then $f$ is said to be strictly Schur-increasing.”

Definition 4.3 (printed p. 10): “The $\alpha$-geometry on ${\cal P}^1_n$ is the pull-back geometry induced by the map $A_p(\rho):{\cal P}^1_n \to \mathbb R^n$ defined by”

$$
A_p(\rho):=\begin{cases}p\rho^{1/p}&p\in\mathbb R\setminus\{0\},\\
\log(\rho)&p=\infty,\end{cases}
\qquad p=\frac{2}{1-\alpha}.
$$

Definition 4.4 (printed p. 10): “We denote by $\mathrm{Scal}_p(\rho)$ the scalar curvature of the $\alpha$-geometry (with $p=\frac{2}{1-\alpha}$) at the point $\rho\in {\cal P}^1_n$.”

Conjecture 4.1 (printed p. 11): “Suppose $n>2$. For the function $\mathrm{Scal}_p(\cdot):{\cal P}^1_n \to R$ one has the following properties:

- if $p\in(1,2)$ then $\mathrm{Scal}_p(\cdot)$ is a strictly Schur-decreasing function;
- if $p\in(2,+\infty]$ then $\mathrm{Scal}_p(\cdot)$ is a strictly Schur-increasing function.”

The repository encoding in research line #15145 uses strictly positive normalized `Fin n` real vectors, decreasing merge-sort initial sums for majorization, the logarithmic pull-back metric defined with Fréchet derivatives, and the usual coordinate Christoffel–Ricci contraction. The settling statement concerns only $p=\infty$ and $n\geq3$. Its proof reduces this literal curvature to a rational power-sum formula and strictly increases it under a nontrivial equalizing T-transform. Finite-$p$ clauses and quantum Conjecture 4.2 remain open; the quantum $p=3$ slice has separate research line #15179.

## Verified locator

DOI: 10.1063/1.1834693 (https://doi.org/10.1063/1.1834693)

Source: https://arxiv.org/abs/math-ph/0407007v2
