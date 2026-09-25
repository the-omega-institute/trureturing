---
bibkey: "iyer2025empirical"
authors: "Gautam Iyer and Raghavendra Venkatraman"
year: 2025
title: "Convergence of empirical measures for i.i.d. samples in W^{-alpha,p}"
doi: null
url: "https://arxiv.org/abs/2512.17794v1"
claim: "Proposition 2.2 computes the exact negative-Sobolev second moment of an i.i.d. empirical-measure error; its proof also treats unsmoothed point measures above the Hilbert embedding threshold."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# A collapsed posterior noise measure and its group variation

Iyer and Venkatraman, [arXiv:2512.17794v1](https://arxiv.org/pdf/2512.17794v1),
Proposition 2.2, PDF page 5, gives an exact second-moment identity for an
i.i.d. empirical measure on Euclidean space after Gaussian smoothing.
Section 5, pages 13–14, derives the identity by independence and centering.
The end of that proof permits zero smoothing when the Hilbert smoothness
index exceeds half the dimension. Theorem 1.1 addresses more general
Lp-based negative Sobolev norms. These are antecedents for measuring point
fluctuations in a topology weaker than measure total variation.

Chapter 42 of [the posterior-field volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)
uses a length-four circle, an explicitly normalized Fourier norm, and
conditionally independent but heterogeneous Bernoulli labels only under
its auxiliary law. Its Hilbert second-moment identity is proved directly
by vanishing cross terms. Summability of the Fourier weights proves norm
continuity of a moving Dirac mass for s greater than one half. Neither
that computation nor the threshold is claimed as new. The Euclidean
i.i.d. theorem is not invoked as a theorem about the actual dependent
pair/path observations or their fixed-size posterior.

A second direct methodological precedent is Berend and Kontorovich,
*On the Convergence of the Empirical Distribution*,
[arXiv:1205.6711v2](https://arxiv.org/pdf/1205.6711v2).
Lemma 8, PDF page 5, bounds the expected l1 error of a countable empirical
distribution by the sum of square roots of its probabilities divided by
the square root of sample size. Equation (5) and Theorem 3, page 3,
give the resulting countable-support tail bound when that square-root
sum is finite. The elementary Cauchy–Schwarz step is exactly the
precedent for summing square roots of group intensities. The paper's
fixed countable i.i.d. sampling law differs from the changing arithmetic
groups and conditional label law here. Its l1 convention equals the full
variation norm of the signed error; Chapter 42 also uses full variation,
without a one-half probability-distance factor.

The `repo-derived` content is the actual-model combination. The same
posterior noise that has a resolved Brownian profile collapses to its
own Gaussian endpoint times a Dirac mass in the stated Hilbert norm,
while its aggregated whole-score-group variation grows as Q to the
one-quarter power with an explicit positive constant. Uniform actual
point-group occupancy, a nonlinear square-root Riemann sum and a
summable square-root-intensity tail estimate establish that constant.
Cumulative variance-clock convergence alone does not prove those steps.

The exact fixed-size posterior is handled by one complete label-vector
comparison and the simultaneous subset-center bound from
[Siripraparat–Neammanee's local-probability application](siripraparat2021local.md).
Applying that bound to the positive and negative center-error subsets
controls the sum of absolute errors. Group variation aggregates all
equal-score labels before taking absolute values; summing individual
label magnitudes gives a different statistic. One common data and label
realization couples the measure with the full endpoint and profile.

The conclusion concerns probability and distributional convergence in
the specified Hilbert and compact path spaces. It does not transfer
actual moments through total variation, claim an extra independent
Gaussian amplitude, assert a different path topology, or provide an
all-amplitude or growing-window theorem. The primary precedents delimit
the classical tools; the bounded comparison is not a global originality
certificate.

## First spatial moment after the collapsed mass

Chapter 43 of [the posterior-field volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_POSTERIOR_FIELD.md)
subtracts the exact moving point mass and resolves the first spatial
moment of the same posterior noise. In the explicitly normalized real
negative Sobolev space, differentiation of a moving Dirac mass is a
classical distributional operation. Its spatial derivative is the
negative of its distributional derivative. Fourier summability gives
the stated threshold and continuity directly; those facts are used
inside the model theorem and are not presented as new standalone results.

A direct precedent for the moment/Dirac-derivative expansion is Neyt
and Vindas, *Asymptotic boundedness and moment asymptotic expansion in
ultradistribution spaces*, [arXiv:1906.06232v3](https://arxiv.org/pdf/1906.06232v3)
(2019 preprint, version dated 17 August 2021). Equation (1), PDF page 2,
records the classical expansion with signed moment coefficients and
Dirac derivatives. Definition 1 and equation (19), page 9, specify its
test-function meaning; Theorem 5, page 10, concerns a fixed element of
the stated ultradistribution dual space. These are not norm-uniform
estimates for a changing random posterior measure. Chapter 43 proves
its own Hilbert remainder, weighted environment bounds and exact-center
transfer. No ultradistribution theorem is imported without its topology
and fixed-object hypotheses.

The Hilbert second-moment mechanism has the same elementary independence
and centering basis as Iyer–Venkatraman's Proposition 2.2, discussed
above. The new proof must use weighted second moments of the actual
count-group environment. The unweighted collapsed-measure estimate from
Chapter 42 cannot be divided by the much smaller spatial scale.
Instead a fresh Hilbert-valued exact-center bound follows from the
conditional Bernoulli density ratio: cancel its constant term, then
apply Cauchy–Schwarz and the fourth moment of the unweighted label sum.
This estimate acts directly on the difference-quotient coefficients.
It does not infer actual moments from posterior total variation.

Classical Gaussian random-measure integration describes the resulting
joint law. The dipole coefficient is the first mark integrated against
the same Gaussian noise that supplies the resolved profile. Symmetry
makes it independent of the total mass, while its covariance with each
finite profile value is explicitly nonzero. Subtracting the endpoint
projection to form the bridge preserves this covariance.

The actual-model bridge also proves weighted remote-group control,
including the low-count Poisson tail and the additive actual-row
comparison remainders. On a compact mark interval, exact Stieltjes
integration by parts expresses the first mark as a functional of the
already jointly convergent profile. Weighted tail control then removes
the truncation. This constructs the new coordinate on the same actual
label realization and the same limiting Gaussian noise, jointly with
the old threshold and capacity fields.

The `repo-derived` assertion is restricted to this compensated arithmetic
posterior construction, its exact moving center, and the stated joint
distributional limit. The distributional Taylor expansion, Gaussian
integrals, integration by parts and Sobolev threshold are classical.
No all-amplitude law, actual moment convergence, alternative path
topology or critical-regularity theorem is asserted. The moving center
cannot be replaced by zero merely from its convergence to zero: that
replacement requires control relative to the finer spatial scale.

## Critical logarithmic energy of the shrinking posterior measure

Chapter 48 of [the window-phase volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_WINDOW_PHASES.md)
returns to the original intensity sequence and the same signed measure
from Chapters 42–43. It examines finite Fourier cutoffs at powers of the
inverse spatial contraction scale. Its statement concerns a finite
quadratic statistic, not membership of an atomic measure in the critical
negative Sobolev space.

The logarithmic Fourier kernel is classical. Frerick, Müller and
Thomaser, *A Fourier Integral Formula for Logarithmic Energy*,
Potential Analysis 61 (2024), 685–699,
[DOI 10.1007/s11118-024-10125-9](https://doi.org/10.1007/s11118-024-10125-9),
recall the circle Fourier-series energy formula in equation (1), printed
page 686. Their Theorem 1, printed page 687, states a Euclidean mutual
logarithmic-energy formula with its integrability conditions. For
complex measures, absolute logarithmic integrability is material;
positive measures have a separate existence formulation. The signed
atomic self-energy in the present construction cannot simply be assumed
to satisfy those hypotheses. Every finite Fourier sum is nevertheless
well defined, and the chapter estimates that finite sum directly.

The relevant elementary uniform bound is that the harmonic cosine sum
through frequency N differs by a bounded amount from the minimum of
log N and log inverse separation. Taylor's inequality below the inverse
separation and summation by parts above it prove the bound. Replacing
the harmonic weights with the specified Sobolev weights changes the
kernel by a uniformly bounded amount. These facts remain classical
steps inside the model proof, not newly named mathematical results.

A second antecedent is Wiener's lemma. Cuny, Eisner and Farkas,
*Wiener's lemma along primes and other subsequences*, Advances in
Mathematics 347 (2019),
[DOI 10.1016/j.aim.2019.02.005](https://doi.org/10.1016/j.aim.2019.02.005),
[arXiv:1701.00101v6](https://arxiv.org/pdf/1701.00101v6)
(version dated 18 February 2023), Theorem 1.1, state the classical
Cesàro Fourier-power identity for a fixed finite complex Borel measure:
the limit is the sum of squared atom masses. This motivates the
high-frequency diagonal term. It does not provide a rate uniform in a
changing array of atom locations and random masses. The version's
qualification concerning a separate polynomial return-time example is
unrelated to the classical theorem and no such example is used here.

The `repo-derived` assertion is the simultaneous actual-posterior
transition across logarithmic frequency scales. All distinct count-group
separations have the same leading logarithm. Their off-diagonal terms
therefore retain the square of the same random total mass up to the
inverse contraction scale. Beyond that scale, the extra logarithmic
energy has a deterministic limiting slope, obtained from concentration
of the sum of squared whole-group posterior charges. The endpoint,
resolved profile, bridge and first spatial moment remain on the same
underlying label realization; no independent copy replaces a cross term.

To justify the deterministic slope, compact uniform actual group
occupancy is combined with whole-line tail control. Under the calibrated
product law the group fourth moments give concentration of the squared
charges. A separate absolute exact-center bound controls their change
under posterior centering, and one complete-vector comparison transfers
only probability statements. The uniform Fourier-kernel remainder is
bounded using the number of possible count groups and their squared
charges. This supplies a changing-array estimate that a fixed-measure
Wiener identity alone does not yield.

The result keeps the fixed amplitude, fixed sparsity exponent, original
intensity sequence, and fixed positive compact range of frequency
exponents. It asserts convergence in probability and joint distribution,
not convergence of actual energy moments, finite critical full-spectrum
energy, or a universal shrinking-window theorem. The classical primary
sources delimit the ingredients; the bounded source comparison does not
certify global originality.

## A quadratic fluctuation beneath the deterministic spectral slope

Chapter 49 of [the window-phase volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_WINDOW_PHASES.md)
examines the next fluctuation scale of the same whole-score-group energy.
Its centering is the observed environment's auxiliary variance, not an
unproved rate-level replacement by its limiting constant. The limiting
Gaussian coordinate is jointly independent of the endpoint, compact
profile, bridge and first spatial moment from the same label realization.

Normal limits for quadratic forms are classical. Peter de Jong,
*A Central Limit Theorem for Generalized Quadratic Forms*, Probability
Theory and Related Fields 75 (1987), 261–277,
[DOI 10.1007/BF00354037](https://doi.org/10.1007/BF00354037),
Definition 2.1, printed page 263, defines clean quadratic forms through
vanishing conditional expectations with independent underlying inputs.
Theorem 2.1, page 264, assumes negligible normalized row variance and a
normalized fourth moment tending to three. Both assumptions matter: the
following discussion explains that negligible row variances alone allow
a nonnormal chi-square limit. Theorem 5.2 gives another sufficient
criterion using tails and eigenvalues for an independent-input quadratic
form with zero diagonal.

Those results are antecedents for quadratic Gaussian limits, not
theorems about dependent actual observations or the exact fixed-size
posterior used here. The chapter uses the simpler independent group-array
Lyapunov theorem after conditioning on the observed environment. The
fourth moment of a centered squared group sum follows by expanding the
eighth moment of bounded independent labels. Mixed linear and quadratic
forms satisfy the same criterion. Only after their joint Gaussian limit
is established do vanishing mixed third cumulants prove independence.
The independent-array theorem, moment expansions and Cramér–Wold step
remain classical ingredients inside the model proof.

The additional actual-model obligation is a squared variance clock.
Ordinary cumulative variance convergence does not determine the sum of
squared group variances. Compact uniform point occupancy provides that
clock locally; the actual one- and two-row estimates bound second
moments of remote group occupancy and remove the cutoff. No four-row
actual comparison or independence of observed rows is assumed. These
estimates identify the explicit integral of the squared Gaussian
intensity as the quadratic fluctuation variance.

The sharper noise scale also requires a sharper use of the existing
exact-center bound. Its explicit rate makes the displacement of the
whole-group coefficient vector negligible after the new normalization.
A single full-window posterior comparison then transfers bounded tests
and events. Auxiliary moment calculations are not promoted into
convergence of actual unbounded quadratic moments.

The environment center is essential at the stated resolution: convergence
to a constant alone permits a displacement of order the fourth root of
the grid size, which diverges after division by its square root. Likewise,
alternating the variance mass between adjacent groups preserves the
cumulative clock but doubles its squared-clock limit. These are
counterexamples to insufficient inference rules, not counterexamples
within the actual observation model.

The finite high-frequency difference slope from Chapter 48 has a
remainder small even at this finer scale. It therefore carries the same
quadratic Gaussian coordinate. The random low-frequency mass term
cancels in its leading difference, with the cutoff-floor residual
controlled separately. This connects the spectrum and the grouped
posterior statistic without introducing a new independent label sample.

The `repo-derived` content is the actual squared-clock and posterior
transfer together with this same-realization second-order spectral law.
The assertion keeps the original intensity, fixed amplitude and beta,
fixed profile windows and fixed frequency exponents. It does not replace
the environment center by a constant without a convergence rate, assert
actual moment convergence, or import old-field jointness from marginal
limits. The comparison with classical quadratic-form theory is bounded
and does not certify global originality.

## Resolving the critical spectral transition

Chapter 50 of [the window-phase volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_WINDOW_PHASES.md)
resolves the cutoff at a fixed multiple of the inverse cluster width.
After subtracting the logarithmic total-mass square, the actual posterior
spectrum converges to a random curve built from the Fourier transform of
the same real Gaussian noise that supplies the spatial profile. Finite
resolved frequency bands remain random even conditional on the endpoint.
This is a finer statement than the leading logarithmic slope law.

Gaussian limits of empirical characteristic functions and quadratic
spectral functionals are classical subjects. John T. Kent,
*A weak convergence theorem for the empirical characteristic function*,
Journal of Applied Probability 12(3) (1975), 515–523,
[DOI 10.1017/S0021900200048324](https://doi.org/10.1017/S0021900200048324),
is a historical antecedent identified by its publisher abstract. Its
full theorem conditions are not used here. The chapter proves its own
conditional Fourier tightness from the already established actual
weighted variance clock and the independent auxiliary labels.

Richard A. Davis, Muneya Matsui, Thomas Mikosch and Phyllis Wan,
*Applications of Distance Correlation to Time Series*,
[arXiv:1606.05481v1](https://arxiv.org/abs/1606.05481v1),
Theorem 3.2 and Appendix A, Lemma A.1, are closer functional antecedents.
They establish Gaussian characteristic-function fields on compacts and
separate near-zero bounds for integrated squared fields under stationary
mixing, marginal/product moment and weight-integrability assumptions.
These mechanisms do not directly handle the present triangular posterior
label array, its random total mass, or its exponentially moving cutoff.
The chapter supplies those actual-model obligations explicitly.

Thomas Mikosch and Yuwei Zhao,
*The integrated periodogram of a dependent extremal event sequence*,
[arXiv:1503.04022v1](https://arxiv.org/abs/1503.04022v1),
[DOI 10.1016/j.spa.2015.02.017](https://doi.org/10.1016/j.spa.2015.02.017),
Theorem 15, is a functional Gaussian limit for the centered integrated
periodogram of a stationary regularly varying sequence. Its assumptions
include Condition (M1), anti-clustering and mixing-rate requirements,
summability of the extremogram, and a nonnegative Holder-continuous
weight with exponent greater than three quarters. It does not apply
directly to the conditional fixed-size posterior field here. In
particular, the singular inverse-frequency weight and the changing
microscopic cutoff require separate estimates.

Norbert Henze and Maria Dolores Jimenez-Gamero,
*Logarithmic energy distances and Gini covariance for Hilbert-valued
random elements*, [arXiv:2606.18365v1](https://arxiv.org/abs/2606.18365v1),
Section 4.1 and Theorem 4.1, study independent two-sample observations
under equality of distributions and a finite squared logarithmic-distance
moment. Their degenerate-kernel formulation is an antecedent for
non-Gaussian quadratic limits. The finite logarithmic moment excludes
positive-probability collisions between independent copies; the present
actual score law is atomic. Neither the independent-sample model nor its
diagonal integrability is silently imported into the posterior problem.
There is also an internal normalization discrepancy in v1: equation (4.2)
makes N times the Gini statistic equal to nm/N times the energy statistic,
whereas the two displayed limits in Theorem 4.1 differ by an additional
factor p(1-p). No normalization formula from that theorem is used here.

The deterministic calculation uses the classical harmonic-sum constant,
a summable correction between the Sobolev weights and reciprocal
integers, and a Riemann-sum estimate for an absolutely continuous
function divided by its argument. Subtracting the value at zero is
essential. An H1 bound controls that subtraction uniformly, including
the first frequency cell. The zero Fourier mode and both signs of the
frequency determine the explicit finite constant. These are classical
analysis ingredients within the model-specific argument.

The Gaussian field is driven by a real random measure. Both its ordinary
covariance and its covariance without complex conjugation must therefore
be retained. Its odd sine component is independent of the even cosine
component and the endpoint; its nonzero quadratic contribution proves
positive conditional band variance. Gaussian conditioning and fourth
moment identities remain classical and concern the limit object only.

The `repo-derived` contribution is the actual posterior H1 control and
exact-center transfer, the uniform constant-order cutoff expansion, and
the common-realization spectral curve with its residual conditional
randomness. The result keeps fixed frequency intervals and fixed
additive logarithmic cutoff intervals. It does not assert actual energy
moment convergence, a finite full critical Sobolev norm, a uniform
second-order expansion over fixed macroscopic exponent intervals, or
an unrestricted growing-frequency theorem. This comparison is bounded
and does not certify global originality.
