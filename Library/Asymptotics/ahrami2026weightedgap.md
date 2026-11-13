---
bibkey: ahrami2026weightedgap
authors: Mohammed Ahrami
year: 2026
title: On the fundamental spectral gap of weighted Schrodinger operators
doi: 10.48550/arXiv.2605.24560
url: https://arxiv.org/abs/2605.24560v1
claim: Open Problem 3.3 asks whether every convex potential has fundamental weighted Dirichlet gap at least that of the zero potential for each positive concave weight.
strata_touched:
  - D5/S3/Analytic/SpectralGap/WeightedConvexPotentialRefutation
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Asymptotics/ahrami2026weightedgap -->
# Convex potentials and positive concave weights

## Verified locator

DOI: 10.48550/arXiv.2605.24560

Source: https://arxiv.org/abs/2605.24560v1

## Source statement

Open Problem 3.3, Section 3.2, p. 10:

> Let $w$ be a positive concave weight on $[0,\pi]$. Does the constant potential minimzer the fundamental spectral gap over the class of convex potentials. Equivalently,
>
> $$\Gamma[V,w]\geq \Gamma[0,w]$$
>
> for every convex potential $V$.

Definition 3.1, Section 3.1, p. 4:

> For $1<M \le \infty$ and $0 < N_{<,>} < \infty $, let
>
> $$\mathcal{C}_M=\lbrace V(x): 0\le V(x)\le M : V(x)\textrm{ is convex on }[0,\pi]\rbrace .$$
>
> and
>
> $$\mathcal{S}_{N_{<,>}}=\lbrace w(x): N_<\leq w(x)\leq N_>: w(x)\textrm{ is concave on }[0,\pi]\rbrace .$$

Section 2 studies $-u''+Vu=\lambda wu$ with $u(0)=u(\pi)=0$,
bounded measurable coefficients, and positive weight. The fundamental gap
is $\lambda_2(V,w)-\lambda_1(V,w)$.

## Encoding and scope

The real functions are unrestricted outside the spatial interval. Trial
functions have their zero extension fixed outside its interior. Index zero
of the positive ordered min-max sequence denotes $\lambda_1$; index one
denotes $\lambda_2$. The statement asserts the existence of both spectra.
The potential bound belongs to `WithTop ℝ`, retaining the finite boundedness
condition when the upper class parameter is infinite.

The fixed pair is $V(x)=x/100$ and $w(x)=1+(x-\pi/2)/100$, with
$M=2$, $N_<=1/2$, $N_>=3/2$. A certificate for the shooting series connects
the four root brackets to the first two min-max values. This concerns the
displayed comparison with zero potential. It does not assert that the pair
beats every ordinary constant potential. Lavine's unweighted result is
outside the scope of this weighted example.

## Computation and literature boundary

The external exact computation is in
`the-omega-institute/trureturing-experiments`, commit
`52aded4b71359d83032e504d3d877b5a8aa9322c`, at
`docs/reports/weighted-gap-convex-potential/check.py`.
Its SHA-256 is
`70ca2ca848f61a5e19b80e3f60370ba79528f961c9f64a5c8678e7e3a776514a`.
The command `python3 docs/reports/weighted-gap-convex-potential/check.py`
has the preregistration reading exit 0 and final line `ALL_CHECKS_OK`.
The Lean certificate uses degree eighty and its own uniform remainder
bound; the external checker uses degree 160.

The literature screen in issue #27107 is partial. Completeness of the
priority search is ASSUMED-UNVERIFIED. A perturbative expansion, an interval
of positive slopes, and conclusions for symmetric weights remain open.
