---
bibkey: li2026splitcif
authors: Hao Li
year: 2026
title: "Conjecture About Arbitrary Even-Order Convexity of w-Optimization of the Split CIF"
doi: null
url: https://arxiv.org/abs/2606.27260v1
claim: "The split covariance intersection w-optimization has nonnegative derivatives of every positive even order for both log determinant and trace."
strata_touched:
  - D5/S3/Estimation/SplitCovarianceIntersectionEvenConvexity
license: citation-only
triage: anchor
---

# Arbitrary even-order convexity of the split CIF

Section 2.1, p. 2, equation (1):

Matrices mentioned in this paper are symmetric matrices by default. Given matrices $\mathbf{P}_{1d}$, $\mathbf{P}_{1i}$, $\mathbf{P}_{2d}$, and $\mathbf{P}_{2i}$ that are positive semi-definite, i.e., $\mathbf{P}_{1d} \geq \mathbf{0}$, $\mathbf{P}_{1i} \geq \mathbf{0}$, $\mathbf{P}_{2d} \geq \mathbf{0}$, $\mathbf{P}_{2i} \geq \mathbf{0}$. Besides, the matrices $\mathbf{P}_{1d} + \mathbf{P}_{1i}$ and $\mathbf{P}_{2d} + \mathbf{P}_{2i}$ which normally correspond to covariances of certain estimates are always positive definite, i.e., $\mathbf{P}_{1d} + \mathbf{P}_{1i} > 0$ and $\mathbf{P}_{2d} + \mathbf{P}_{2i} > 0$. For $w \in [0,1]$, define
$$
\begin{aligned}
\mathbf{P}_{1}(w) = \mathbf{P}_{1d}/w + \mathbf{P}_{1i},  \\
\mathbf{P}_{2}(w) = \mathbf{P}_{2d}/(1-w) + \mathbf{P}_{2i},  \\
\mathbf{P}(w) = (\mathbf{P}_{1}(w)^{-1} + \mathbf{P}_{2}(w)^{-1})^{-1}.
\end{aligned}
$$
When $w=0$ or $w=1$, $\mathbf{P}(w)$ denotes the limit value as $w \to 0$ or $w \to 1$ respectively.

Section 2.2, p. 3, definition (6):

For a generic function $f(x)$, if its $m$-th-order derivative is always non-negative (or positive semi-definite), namely
$$
\frac{d^m}{dx^m} f(x) \geq 0,
$$
then it is said to have the **$m$-th-order convexity** [16].

Section 2.2, p. 3, conjecture (7a), (7b):

The proposed conjecture is that **the $w$-optimization problem has arbitrary even-order convexity**, more specifically, for $k \in \{1, 2, 3, \cdots\}$ we always have

$$
\begin{aligned}
\frac{d^{2 k}}{d w^{2 k}} \ln \det(\mathbf{P}(w)) \geq 0,  \\
\frac{d^{2 k}}{d w^{2 k}} tr \{ \mathbf{P}(w) \} \geq 0,
\end{aligned}
$$

The real matrices A, B, C, D encode the four source matrices in their displayed order.
Scalar division is multiplication by the reciprocal scalar. The formal statement retains
positive semidefiniteness of each matrix and positive definiteness of the two pair sums;
it covers every positive even derivative order at every weight strictly between 0 and 1.
The source's endpoint limit convention is not part of that statement.

## Verified locator

- URL: https://arxiv.org/abs/2606.27260v1
- Original source: https://arxiv.org/src/2606.27260v1, `LI_Hao_CAEOCWO.tex`.
- Scope: Section 2.1, equation (1), for the covariance and semidefinite hypotheses;
  Section 2.2, equation (6), for order convexity, and equations (7a)–(7b) for both
  arbitrary positive even-order derivative inequalities.
