---
slug: oeis-a079063-sqrt-prime-gap-lower-bound-refutation
bibkey: cloitre2003a079063
doi: null
url: https://oeis.org/A079063
triage: theorem
motivation_gids:
  - D5/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation
---

# Refutation of the A079063 square-root prime-gap lower-bound conjecture

## Problem

OEIS A079063, NAME (verbatim):

> Least k such that sqrt(prime(n+k))-sqrt(prime(n))>1

COMMENT (verbatim):

> Inspired by Andrica's conjecture. If it is true, a(n)>1 for all n.

FORMULA (verbatim; Benoit Cloitre, Feb 02 2003):

> Conjecture: there is a constant c>0 such that for n large enough, a(n)>c*sqrt(n) and we can take c=0.4. More precisely, there are 2 constants A and B such that A=lim sup n ->infinity a(n)/sqrt(n) exists = 0.75....; B=lim inf n ->infinity a(n)/sqrt(n) exists =0.46.... - _Benoit Cloitre_, Feb 02 2003

The literal object is `a(n)`, the least `k >= 1` such that
`sqrt(p_(n+k)) - sqrt(p_n) > 1`, where `prime(n) = p_n` is the n-th
prime. The refuted claim is its weakest quantified eventual lower-bound form:
there exist `c > 0` and `N` such that every `n >= N` satisfies
`a(n) > c*sqrt(n)`. This refutes the proposed `c = 0.4` and the claimed
positive `liminf = 0.46...` a fortiori. The existence or value of either
limsup or liminf is not formalized.

## Motivation

The conjecture was added to OEIS A079063 in 2003. Refuting even its weakest
eventual positive lower-bound form settles both displayed positive constants
without making a stronger assertion about the sequence at individual indices.

## Gap

Preregistration issue #7507 and its probe report record searches dated
September 13, 2026. All twelve OEIS revisions, #1 through #12, were read; the
formula is present from revision #1, and none gives a proof or refutation.
The arXiv web search returned 0 results, while the API returned HTTP 429.
OpenAlex returned 0 results, MathOverflow returned 0 results, and GitHub
repository search returned 0 results. GitHub code search returned HTTP 404 and
is `ASSUMED-UNVERIFIED`. These are bounded search surfaces, not an exhaustive
literature claim.

## Route

Assume constants `c > 0` and `N` provide the claimed lower bound. Choose a
natural `r` with `c*r > 1`. Minimality of `a` gives the local step
`sqrt(p_(t+m)) <= sqrt(p_t) + 1` whenever `t >= r^2*m^2`. Iterating this step
over a block of length `L = 3*r^2` and then inducting on `m` gives a constant
`B > 0` such that
`sqrt(p_((r*m)^2)) <= B*m` for all sufficiently large `m`.

Consequently `p_((r*m)^2) <= B^2*m^2`, so
`pi(B^2*m^2) >= r^2*m^2`. Mathlib's
`Chebyshev.eventually_primeCounting_le` gives
`pi(x) <= (log 4 + epsilon)*x/log x` eventually. At `x = B^2*m^2`, its
coefficient tends to zero, contradicting the preceding fixed positive
quadratic lower bound as `m` tends to infinity.

## Falsifier

The refutation would fail if the `sInf` witness set were empty at a positive
index used by the argument, if minimality did not imply the local one-unit
increment bound, if the `L = 3*r^2` block failed to span consecutive quadratic
indices, if the resulting linear prime-root bound did not imply the stated
prime-counting lower bound, or if the cited Chebyshev bound did not hold in the
pinned library.

## Evidence

- Lean module:
  `D5/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation.lean`.
- Main theorem: `result : not claim`, with exactly the std3 axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- The proof is symbolic; no finite kernel certificate is claimed.
- The orchestrator's sieve to approximately `4.6*10^6` gave
  `a(n)/sqrt(n) = 0.601, 0.550, 0.528, 0.495` at
  `n = 10^3, 10^4, 10^5, 3*10^5`, decreasing on that sample like
  `2/sqrt(log n)`.
- The probe's sieve to `2*10^5` gave `a(1000) = 19` and
  `a(10000) = 55`.

The numerical observations motivate the asymptotic route but do not carry the
result. The Lean proof derives the contradiction from minimality, block
iteration, and the pinned Chebyshev prime-counting estimate.

## Triage

`theorem`. The formal result refutes the weakest eventual positive lower bound,
and therefore the displayed `c = 0.4` and positive-liminf claims. It asserts no
corrected asymptotic and no claim about unverified individual indices.

The module is classified `utility: none`: its new content is a symbolic
asymptotic estimate chain, not a finite computation or verifiable instance as
its main content. None of `bounded-enumeration`, `checker`,
`numeric-reduction`, or `certified-instance` applies. The declarations `claim`
and `result : not claim` remain an ordinary definition and theorem, and the
open-problem resolution kind remains `Refuted`.

## ASSUMED-UNVERIFIED

The arXiv API search was blocked by HTTP 429, GitHub code search returned HTTP
404, and all literature searches were bounded. The orchestrator and probe
numerical readings above were supplied by issue #7507 and were not recomputed
by this implementation seat. Nothing here claims a result about Andrica's
conjecture or establishes the existence or value of the proposed limsup or
liminf.
