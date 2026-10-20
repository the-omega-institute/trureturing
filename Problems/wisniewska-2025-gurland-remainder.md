---
slug: wisniewska-2025-gurland-remainder
bibkey: wisniewska2025gurland
doi: null
url: https://arxiv.org/html/2512.07028v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.result
---

# Gurland's original logarithmic remainder

## Problem

Halina Wiśniewska, *Some inequalities for Gurland's ratio of the gamma
functions*, arXiv:2512.07028v1, section 2, Open Problem 1:

> In Corollary 1 we showed that R_n^m(x,y) tends to zero under a sufficient
> condition. Does R_n^m(x,y) tend to zero hold for every x,y > 0?

For positive real x,y put a=(x+y)/2 and d=(x-y)/2. In equations (2)–(4),

$$
G_* = \frac{\Gamma(1+x)\Gamma(1+y)}{\Gamma(1+a)^2},\qquad
H(s,b)=\sum_{j=0}^{\infty}\frac1{(j+b)^s},
$$
$$
S_m=\sum_{k=1}^{m-1}\frac{d^{2k}H(2k,1+a)}{k},\qquad
R_m=\log G_*-S_m.
$$

The expansion order m tends to infinity through integers, with m >= 2
in the source. Its n is already summed out. Every positive real pair,
including x=y and positive integer Gamma arguments, is in scope.

## Motivation

`D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.result` has type
`claim`. The closed proposition `claim` is precisely the all-positive
limit above. The source's sufficient condition Q(x,y)<1 is unnecessary.

## Gap

Preregistration [#18508](https://github.com/the-omega-institute/trureturing/issues/18508)
binds the source, tier-1 question, full quantifiers and bounded literature
scope. The source year is 2025. The inspected versioned primary poses
the question. The bounded bibliographic input covers related Crossref
titles and Merkle 2005, DOI 10.1016/j.camwa.2004.01.016, metadata.
No exact prior settlement was established in that bounded scope.
Merkle's full mathematical text remains unverified. This is no priority
claim or certification that earlier work lacks the identity.

## Route

For n >= 0 put c_n=d^2/(n+1+a)^2. The identity

$$
1-c_n=\frac{(n+1+x)(n+1+y)}{(n+1+a)^2}
$$

and positivity give 0 <= c_n < 1. In the real Euler logarithmic sequence
at 1+x, 1+y and 1+a, the factorial and log(N) contributions cancel.
Consequently the sum of -log(1-c_n) is exactly log(G_*). This uses the
all-positive real Gamma limit and retains integer arguments.

The logarithmic power series has nonnegative terms c_n^(k+1)/(k+1).
Its joint summability follows from the summable logarithmic row sums.
The source Hurwitz columns are separately summable by p-series comparison.
Exchanging the sums identifies the coefficient series with log(G_*).
Finite interchange and the index k+1 identify its partial sums with the
source S_m. Their convergence proves R_m tends to zero.

## Falsifier

A mismatch in the Gamma shift, the real Hurwitz shift, the exponent 2k,
the finite interval 1 <= k < m, or the limit parameter would invalidate
the source correspondence. These quantities occur explicitly in the
formal definitions and in the finite Euler and interchange identities.
No arbitrary Taylor-point family is substituted for the source remainder.

## Evidence

The formal module contains `sourceHurwitz`, `gammaRatio`,
`partialExpansion`, `remainder`, `claim` and `result : claim`, with only
helpers used in their proof. The finite Euler cancellation, positive-shift
summability, finite interchange, sum exchange and diagonal calculation
are kernel proof terms. Classical summation and Gamma theorems are
reused from the pinned library. The mathematical result introduces no
axiom, `sorry`, `admit`, `native_decide` or certificate-trust assumption.
Its axiom closure and current build evidence are supplied by the normal
Lean report; this prose is not a second machine status.

## Triage

### What the settlement shows

The mechanism is the exact nonnegative logarithmic double series, whose
row sums are fixed by the all-positive Gamma Euler limit. The theorem is
pointwise on the entire positive quadrant; no global uniform rate or
stronger quantitative remainder estimate is asserted. At x=y, G_*=1
and every S_m and R_m equals zero. This branch is included directly.

The equivalent identity in Open Problem 2 has zero difference and belongs
to the same family, rather than a second problem settlement. Open Problem
3, concerning the location of t(x,y), is unresolved. The source's proved
Q<1 special case remains a special case of the whole-domain result.
The diagonal uses equation (4) and never asserts existence in the empty
interval (0,c_n). Source-selected Taylor points off the diagonal must
satisfy equation (14); no such points are exposed by the native claim.

## ASSUMED-UNVERIFIED

Exact overlap with Merkle's full text and wider literature priority remain
unverified. Formal correctness of this source statement does not settle
priority, independent acceptance, integration or a solved-problem count.
