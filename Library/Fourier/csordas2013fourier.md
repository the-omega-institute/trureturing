---
bibkey: csordas2013fourier
authors: George Csordas
year: 2013
title: Fourier transforms of positive definite kernels and the Riemann xi-Function
doi: null
url: https://arxiv.org/abs/1309.0055v2
claim: Theorem 4.2(b) states strict concavity of log(Phi(sqrt(t))) for t>0 and attributes it to Csordas--Varga (1988), Theorem 2.1; Remark 4.3(a) states the corresponding strict radial curvature inequality.
strata_touched:
  - D5/S3/Analytic/Fourier/ThetaRadialCurvature
license: citation-only
triage: anchor
---

# Classical square-variable concavity of the theta kernel

## Verified locator

- URL: https://arxiv.org/abs/1309.0055v2

The retained primary version is the cited arXiv v2 text; Theorem 4.2(b) and
Remark 4.3(a) are the canonical theorem locations used by the Scribe.

For the kernel K in equation (4.2), Theorem 4.2(b) states that
log K(sqrt(t)) is strictly concave for every t>0. It explicitly attributes this
result to reference [21], Theorem 2.1: G. Csordas and R. S. Varga, Moment
inequalities and the Riemann hypothesis, Constructive Approximation 4 (1988),
175--198. Remark 4.3(a) gives the equivalent strict inequality
t*((K'(t))^2-K(t)*K''(t))+K(t)*K'(t)>0 for t>0.

The repository uses the Romik normalization Phi(x)=2*K(x/2). Thus
log Phi(sqrt(r))=log 2+log K(sqrt(r/4)), preserving strict concavity on r>0.
The corresponding radial curvature expression for Phi at x equals twice the
expression for K at x/2. Both public clauses are therefore literature-attested.

The repository proof uses its fixed full theta series, derivative polynomials,
the exact first two modes and a bound on the complete infinite n>=3 tail.
It is a concrete formal proof of this known result, not a new concavity claim
or a proof of the Riemann hypothesis. The cited 1988 attribution is read from
the 2013 primary text; no independent verification of the entire 1988 paper
is asserted here.
