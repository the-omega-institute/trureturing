---
bibkey: drtonsullivant2007algebraic
authors: Mathias Drton and Seth Sullivant
year: 2007
title: Algebraic Statistical Models
doi: 10.48550/arXiv.math/0703609
url: https://arxiv.org/abs/math/0703609v1
claim: "Discrete conditional independence is characterized by the cross-product quadratic equations on each conditioning fiber; strictly positive categorical probabilities have log probability-ratio coordinates."
strata_touched:
  - D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope
license: citation-only
triage: anchor
---

# Discrete conditioning fibers and positive probability ratios

The consumed primary text is
[Algebraic Statistical Models, arXiv:math/0703609v1](https://arxiv.org/pdf/math/0703609v1).
Section 3.2, Example 16, PDF p. 13, states that
$X_1\perp X_2\mid X_3$ is equivalent to the equations

$$
p_{i_1j_1k}p_{i_2j_2k}-p_{i_1j_2k}p_{i_2j_1k}=0
$$

for every pair of values of each of the first two variables and every
conditioning value $k$. This is an equation on the joint probabilities,
not a requirement that every conditioning event have positive mass.
For a positive-mass binary fiber its normalized table is independent
exactly when its determinant is zero. At zero mass every nonnegative
cell is zero, and no conditional distribution is asserted.

Example 4, PDF pp. 4–5, uses the natural coordinates
$\eta_x=\log(p_x/p_m)$ for strictly positive categorical probabilities.
It identifies the full interior of the probability simplex with these
coordinates. It does not extend a finite ratio parameterization to cells
of zero probability.

The [determinant and native guard volume](../../docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_DETERMINANT_AND_NATIVE_GUARD_CONTINUATION.md)
uses Example 16 for the conditional binary table on $z=0$ and Example 4
for positive ratios relative to the empty cell. Its conditional covariance,
separator normalization, odds ratio and target residual are elementary
finite-table consequences shown there. The paper supplies the classical
statistical ingredient; the native high-to-low FIB reader, its actual
reply archive and continuing guard task are supplied by the project.
No source acquisition, native instrument, physical or formal certification
is attributed to this reference.
