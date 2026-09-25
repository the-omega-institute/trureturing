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

# Threshold groups and several separated rank boundaries

Chapter 36 of [the posterior threshold volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)
applies the martingale theorem to a forward threshold-strip process under the calibrated independent Bernoulli
law. All labels at the same observed score jump together. Small individual
label increments therefore do not verify the theorem's jump hypothesis.
The proof first establishes uniform convergence of a monotone variance
clock to a continuous function. This bounds the largest score-group variance.
The independent Bernoulli fourth-moment bound then controls the sum of all
grouped fourth moments, implying the required expected maximum squared-jump
bound. A deterministic time change reduces the limiting clock to linear
time, as required by Whitt's stated theorem.

The threshold tail is reconstructed from a terminal tail variable and a
forward strip martingale with the correct strict/non-strict endpoint
conventions. This supplies a right-continuous finite process even when the
nonlattice score law has atoms. It does not reverse a step process and assume
that its path remains right-continuous. Nonlattice fixed-width localization
is attributed to [Stone](stone1967local.md), and the one-union posterior
comparison and weighted exact-center bound use the local input described in
[Siripraparat–Neammanee](siripraparat2021local.md).

The new `repo-derived` statement couples the entire compact threshold-tail
field to finitely many separated critical-capacity processes in the actual
stationary pair/path experiments. The common coarse origin is proved using
actual interval-count variance and exact means. Joint Gaussian convergence
establishes independence between the threshold field and the primitive
boundary processes before their common random translation. Their absolute
fine values retain dependence through that shared origin; their relative
increment processes have an origin-independent product law. The covariance
identities concern the limiting random variables only.

Monotone-clock convergence, martingale functional limits, Brownian tail
covariance and stationary increments are classical auxiliary facts. Neither
the martingale theorem nor the conditional-design independence mechanism
alone provides this actual-model joint law, its grouped-atom verification,
or its common exact posterior centers. This attribution concerns the checked
proof ingredients and does not certify global originality. The result does
not assert a fine-scale process over continuously varying thresholds, a
shrinking-threshold tangent limit, or convergence of actual moments.


# A Gaussian endpoint inside a collapsing score cluster

The same primary paper also states the classical tightness criterion in
Theorem 3.2, printed page 279. Equations (14)–(15) define the ordinary and
partition oscillation moduli. Tightness requires the partition modulus to
vanish in probability as its mesh parameter tends to zero. The partition
uses half-open intervals and controls the spacing of its internal points;
the stated half-line version has a separate last-interval convention.
An ordered triple collapsing at an interior point encounters at most one
partition point. Hence one of its adjacent increments is bounded by a
within-partition oscillation. Two adjacent increments that both stay
nonzero with positive probability violate this necessary condition.
This criterion and its elementary three-point consequence are classical.

Chapter 39 of [the posterior threshold volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)
constructs one fixed nonlattice amplitude with exceptionally accurate
rational approximations to its logarithmic jump ratio. On a legal
subsequence, an entire rational line of count pairs fits inside the
microscopic score window. Uniform Stirling estimates and a Riemann sum,
with relative tail control, calculate its comparison mass. Actual
one/two-row estimates, compensation and exact untilting transfer the
mixed occupancy. One posterior-vector comparison and variance-weighted
center estimate then give a Gaussian endpoint at scale
sqrt(q/(Q sqrt(lambda))). Two disjoint portions of the same count line
produce nondegenerate joint Gaussian increments at three deterministic
score locations tending to zero. Their oscillation violates J1 tightness
even at that endpoint normalization.

The arithmetic approximation, Poisson asymptotics, array Gaussian limits
and topology criterion are established methods. The fixed-amplitude
construction, its actual pair/path transport, sharp posterior scale and
collapsed-cluster obstruction are the `repo-derived` result. An endpoint
Gaussian alone neither proves tightness nor permits replacing the
cluster by one jump. Equal-score labels remain grouped throughout.

For comparison, Borovkov–Borovkov's *A refined version of the integro-local
Stone theorem*, DOI [10.1016/j.spl.2016.12.004](https://doi.org/10.1016/j.spl.2016.12.004),
[arXiv:1607.05879v2](https://arxiv.org/abs/1607.05879v2), imposes the strong
nonlattice characteristic-function condition (2), page 3, in Theorem 1.
Its Remark 1, page 4, already explains a classical atom obstruction to
arbitrarily small intervals. The fixed two-jump compound-Poisson law
here is discrete and does not satisfy that strong condition. Its ordinary
nonlattice status is insufficient to import the refined shrinking-window
estimate. That theorem does not provide the present actual-data,
fixed-cardinality posterior cluster or its process conclusion.

These comparisons delimit the inspected inputs and do not certify global
originality. Chapter 39 asserts no actual moment convergence, universal
amplitude law, or conclusion in another path topology. Its conditional
posterior calculations are on the uniform-support-prior space; the
fixed-support conclusions are unconditional and use equivariance.

# Resolving the cluster by its compensation scale

Chapter 40 of [the posterior threshold volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)
uses the same fixed near-arithmetic amplitude and legal subsequence as
Chapter 39. Its exact compensated score step gives a smaller threshold
scale, asymptotic to epsilon(1-alpha)sqrt(lambda). On the rational count
line, this change of coordinates is exact. The uncompensated central
score differs from the correct center by an unbounded number of these
smaller scale units, despite a negligible difference at the outer-window
scale.

The model-specific result is a compact exact-posterior profile jointly
with its full cluster endpoint and the previous threshold/capacity field.
Its limiting variance clock is a Gaussian distribution function. The
endpoint-centered profile has a Brownian-bridge limit independent of the
endpoint; the whole new Brownian motion is independent of the previous
primitive field before its random translations. These statements concern
one common observation and label vector, not separately sampled marginal
limits.

Whitt's Theorem 2.1(ii), printed pages 270–271, is used on a forward strip
martingale under the calibrated independent Bernoulli law, after a
deterministic change of time makes its limiting predictable variance
linear. Uniform convergence of the monotone variance clock controls the
maximum variance of a whole equal-score group. The Bernoulli fourth-moment
bound controls the expected maximum squared jump. Initial and terminal
tail sums are retained as independent auxiliary coordinates before the
full-vector comparison transfers the endpoint and entire profile to the
exact posterior. The weighted estimate described in
[Siripraparat–Neammanee's note](siripraparat2021local.md) transfers every
prefix center uniformly. It is not obtained by multiplying total
variation by the number of labels.

The martingale theorem, Gaussian time changes, Brownian-bridge covariance
identity, and independence of jointly Gaussian orthogonal coordinates
are classical. The `repo-derived` content is the compensated arithmetic
coordinate, actual mixed-row clock, exact posterior process transfer and
joint separation from the existing scales. The full joint proof verifies
Gaussianity before using small overlap covariances. Its deterministic
conditional limit is adjoined to the common data origin using bounded
continuous origin tests and bounded Lipschitz process tests, as in the
conditional-limit mechanism attributed above to Pasquazzi.

This attribution does not assert global originality. The conclusion is
restricted to the fixed Chapter 39 amplitude, each fixed beta and fixed
compact parameter sets. It asserts neither actual moment convergence nor
a universal microscopic limit for nonlattice amplitudes. The conditional
posterior statements are under the uniform support prior; fixed-support
conclusions use the unconditional permutation-equivariant law.

# The critical arithmetic mesh and Gaussian staircase

Chapter 41 of [the posterior threshold volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)
keeps the fixed amplitude of Chapters 39–40 and changes the legal count
intensity to floor(theta Q squared), for fixed positive theta. Its
compensated score step gives exact integer coordinates on the count line.
The limiting group variances are discrete Gaussian weights, and the
complete fixed-size posterior profile is a Gaussian staircase. The
endpoint has the same sqrt(q/lambda) normalization as the isolated-atom
example, while two nondegenerate group increments still obstruct J1
tightness in the original collapsing score window. An endpoint scale
therefore does not determine a one-jump path law.

This is a different actual-model limit from the continuous profile in
Chapter 40. Each complete count group now has positive limiting variance.
Whitt's continuous Brownian martingale limit theorem cannot be invoked
by claiming its maximum-group-jump condition. Instead, on a fixed compact
interval the jump positions are exactly the same finite set of integers
at every sample size. The proof retains a left-tail variable, the finite
whole-group vector and a right-tail endpoint variable. A bounded-label
joint CLT and the continuous fixed-step reconstruction yield the compact
J1 conclusion, including integer endpoints. Relative summable Poisson
tails establish the full endpoint variance before this finite-vector
argument is used.

The normalized weights are the real one-dimensional discrete Gaussian
in Agostini and Améndola, *Discrete Gaussian Distributions via Theta
Functions*, SIAM Journal on Applied Algebra and Geometry (2019),
DOI `10.1137/18M1164937`, [arXiv:1801.02373v2](https://arxiv.org/abs/1801.02373v2),
equations (2.2)–(2.3) and Definition 2.3, page 3. In their exponential
convention the parameters are u = 0 and B = kappa/(2 pi theta) > 0.
Only this explicitly positive, convergent series is used; no arbitrary
prescribed-moment existence assertion is needed.

Independent Gaussian sums, discrete Gaussian weights, fixed-step path
reconstruction and the Gaussian bridge projection are classical. So are
Whitt's necessary partition-modulus criterion, the exact conditional
Bernoulli representation and the local probability bound described in
[Siripraparat–Neammanee's note](siripraparat2021local.md). The
`repo-derived` content is the critical arithmetic sampling sequence,
its actual mixed occupancy, exact posterior staircase, separation from
the previous field, and an outer-path obstruction despite the matching
endpoint normalization. One complete posterior union and its weighted
center estimate preserve the common realization throughout.

The variance and covariance expressions describe the limiting Gaussian
objects. They assert no actual moment convergence. The result fixes theta,
beta, the amplitude and compact intervals; it does not supply a simultaneous
law for varying theta or all nonlattice amplitudes. Conditional posterior
calculations remain under the uniform support prior, and fixed-support
conclusions use unconditional equivariance and one common direction event.
The attribution delimits the classical tools and does not certify global
originality.
