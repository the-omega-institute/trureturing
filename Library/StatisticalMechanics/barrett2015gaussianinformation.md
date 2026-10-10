---
bibkey: barrett2015gaussianinformation
authors: Adam B. Barrett
year: 2015
title: Exploration of synergistic and redundant information sharing in static and dynamical Gaussian systems
doi: null
url: https://arxiv.org/abs/1411.2832v2
claim: Sections 2–3 give finite jointly Gaussian conditional covariance, entropy and mutual information, and the whole-minus-sum information difference for three scalar Gaussian variables.
strata_touched: []
license: citation-only
triage: anchor
---

# Joint Gaussian conditional information and net information difference

The primary text is [arXiv:1411.2832v2, §§2–3](https://arxiv.org/html/1411.2832v2).
Section 2, equations (5)–(6), gives the Schur conditional covariance and the
observation-dependent conditional mean. Equations (7)–(14) give differential
entropy, the information chain rule, and the Gaussian determinant formulas.
The continuous variables have densities with respect to Lebesgue measure;
the displayed inverses and finite logarithms require nonsingular covariances.

Section 3, equations (15)–(20), treats a positive-definite three-variable
correlation matrix with off-diagonal entries $a,b,c$. Its whole-minus-sum
quantity is

$$
\begin{aligned}
\operatorname{WMS}(X;Y,Z)
&=I(X;Y,Z)-I(X;Y)-I(X;Z)\\
&=I(X;Y\mid Z)-I(X;Y)\\
&=\frac12\log\frac{(1-a^2)(1-b^2)(1-c^2)}
{1-a^2-b^2-c^2+2abc}.
\end{aligned}
$$

This difference is net synergy minus redundancy in the paper's terminology;
it does not by itself specify all parts of a partial information decomposition.

[The legal parity-source application, Theorem 27.4](../../docs/develop/theory/AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md)
consumes this formula with $X=Y_A$, $Y=Y_B$, $Z=Y_C$ and
$\mathcal U=-\vartheta\operatorname{WMS}$. Its independent calibrated noises,
common Gaussian source, rank-one interventions and source-to-control map are
additional declared data. The paper supplies the information identity, not the
weighted five-edge determinant polynomial or the legal parity-source target.
No article text, figure or supplementary material is reproduced here.
