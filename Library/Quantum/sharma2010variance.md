---
bibkey: sharma2010variance
authors: Rajesh Sharma, M. Gupta, G. Kapoor
year: 2010
title: Some better bounds on the variance with applications
doi: null
url: https://jmi.ele-math.com/04-32/Some-better-bounds-on-the-variance-with-applications
claim: Popoviciu's range-squared-over-four bound gives the spectral half-width variance bound, which combines with Cauchy-Schwarz and finite support counting to bound the sparse covariance sum.
strata_touched:
  - D5/S3/Quantum/Information/CovarianceSumBound
license: citation-only
triage: anchor
---

# Popoviciu's bound and the spectral covariance sum

## Verified locator

The exact upstream locator is:
https://jmi.ele-math.com/04-32/Some-better-bounds-on-the-variance-with-applications

The publisher's article page was retrieved successfully. It gives the title,
the three authors above, DOI 10.7153/jmi-04-32 and the volume-4, issue-3 placement
in Journal of Mathematical Inequalities. This note binds the publisher URL.

The round-17 seat reports the citation as Journal of Mathematical Inequalities
4(3), 355–363 (2010), and specifically printed page 355: equation (1.3) defines
r = M−m and equation (1.4) states Popoviciu's bound S² ≤ r²/4.
These page and equation readings are seat-reported, not checked in the PDF here.

## Scope of the dependency

For a Hermitian A with spectrum in [c−Δ,c+Δ], Δ ≥ 0, a positive trace-one
density D induces a probability distribution on the spectral values. Its
variance is the repository's Var_D(A). The weighted form of the range bound
can be checked directly: for a random variable X in [m,M], with mean μ,

    E[(X−m)(M−X)] ≥ 0,
    Var(X) ≤ (M−μ)(μ−m) ≤ (M−m)²/4.

This argument works for arbitrary nonnegative spectral weights, including
zero weights, so it does not assume an invertible density or a uniform sample.
Taking m = c−Δ and M = c+Δ gives Var_D(A) ≤ Δ². The repository realizes
this same bound through continuous functional calculus and the positive
expectation of a centered square. Its existing `variance_le_half_width_sq`
Mathlib citation remains intact.

For `covariance_sum_le`, apply that variance bound to every R_x and then use
the Cauchy-Schwarz and support-counting chain written out in
`D5/L/Quantum/axler2024innerproduct`:

    |Cov_D(R_x,R_y)| ≤ sqrt(Var_D(R_x) Var_D(R_y)) ≤ Δ²,
    Σ_{x,y∈Q} |Cov_D(R_x,R_y)| ≤ |Q| b Δ².

The support size b is supplied as a hypothesis. The paper is cited for the
explicit variance bound, not for a named sparse quantum covariance theorem
or a locality law. The weighted spectral translation and finite summation are
standard direct consequences spelled out here.

## What this note does and does not attest

Attested by this repository's own retrieval: the publisher's article-page
title, authors, DOI and volume/issue placement above.

Not attested here: the article's PDF, printed page 355, equations (1.3) and
(1.4), and the page range 355–363. Those are the round-17 seat's report,
relayed in the implementation brief and issue #6298, and remain
`ASSUMED-UNVERIFIED` as interior readings. That seat explicitly reported
checking the **2010 paper's statement** of Popoviciu's bound. Neither that
report nor this note claims a page-by-page verification of Popoviciu's 1935
original paper. No priority or earliest-appearance claim is made.
