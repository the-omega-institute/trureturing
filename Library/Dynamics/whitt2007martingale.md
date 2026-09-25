---
bibkey: "whitt2007martingale"
authors: "Ward Whitt"
year: 2007
title: "Proofs of the martingale FCLT"
doi: "10.1214/07-PS122"
url: "https://arxiv.org/abs/0712.1929v2"
claim: "Theorem 2.1(ii) gives a multidimensional Brownian limit from predictable quadratic-covariation convergence and negligible martingale and bracket jumps."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Martingale limits and a posterior rank process

The primary text is Whitt, *Probability Surveys* 4 (2007), 268–302,
arXiv:0712.1929v2. Theorem 2.1(ii), printed pages 270–271, assumes locally
square-integrable vector martingales starting at zero. Their predictable
quadratic covariations must converge to a deterministic covariance matrix
times time. Expected maximal bracket jumps and expected squared maximal
martingale jumps must vanish. The conclusion is weak convergence in
Skorohod space to Brownian motion with that covariance matrix. A diagonal
matrix gives independent Brownian coordinates. These are classical results.

Chapter 34 of [the fluctuation volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_FLUCTUATIONS.md)
uses this result only after replacing one entire posterior rank block by a
calibrated independent Bernoulli vector. The two sides have limiting variance
clocks v-plus and v-minus times time, zero cross brackets, jumps at most
q to the power minus one quarter, and bracket jumps at most one over four
square roots of q. The proof also supplies an elementary fourth-moment
interpolation argument for tightness. Neither argument treats the exact
fixed-size posterior partial sums as a martingale.

A closely related primary source is Leo Pasquazzi, *Functional Central Limit
Theorems for Conditional Poisson sampling Designs*,
[arXiv:1905.01021v2](https://arxiv.org/abs/1905.01021v2).
Its Theorem 5 states the joint independence mechanism: a deterministic
conditional process limit is independent of a convergent data-measurable
component. Its sampling FCLTs study Horvitz–Thompson and Hájek processes;
the bounded-inclusion-probability setting and the later small-probability
extension carry their own covariance, Lindeberg and function-class conditions.
The latter extension's assumption B0 has a positive limiting sample fraction.
Those design theorems do not automatically apply to the sparse, data-selected
rank strips here. Chapter 34 proves its conditional path convergence and
joint independence directly on a separable continuous-path space.

The conditioning representation itself is established rejective-sampling
structure; see [Arratia–Goldstein–Langholz (2005)](https://arxiv.org/abs/math/0506300v1).
The quantitative local probability input is attributed separately to
[Siripraparat–Neammanee](siripraparat2021local.md). Classical dyadic maximal
estimates, Brownian stationary increments and conditional Gaussian
covariances remain auxiliary methods. The new `repo-derived` statement is
the joint actual stationary pair/path capacity process: one growing union
label vector, two variance clocks, a common observed rank origin, uniform
mean control and exact minimax centers. The lattice equality condition
for origin-independent increments follows from that process and logistic
variance symmetry. Independence from the absolute fine value at the origin
is explicitly false. The inspected sources do not supply this entire
model-specific bridge; this bounded comparison is not a global novelty claim.
