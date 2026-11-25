---
slug: alexandersson-2026-parking-descent-refinement
bibkey: alexandersson2026parking
doi: 10.48550/arXiv.2609.05131
url: https://arxiv.org/html/2609.05131v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence
---

# Alexandersson Problem 10.3

## Problem

“Refine Theorem 1.2 by descents while retaining a finite local state.”

For each 1 ≤ m ≤ n, take the words of length n on 1 through m whose
nondecreasing rearrangement has its i-th letter at most i, with indices
starting at one. Let Gₙ,ₘ(t,u,v) count these words by strict interior
peaks, adjacent ties and strict adjacent descents. The insertion
recurrence should use a fixed collection of local types, and setting
v = 1 should give Theorem 1.2. [Source](https://arxiv.org/html/2609.05131v2#S10.Thmtheorem3) · [DOI 10.48550/arXiv.2609.05131](https://doi.org/10.48550/arXiv.2609.05131)

## Motivation

The bounded alphabet gives a recurrence for all lengths and upper
bounds. A strict peak couples the comparisons on its two sides, so
a product over single comparisons requires a paired block at each
old strict peak.

## Gap

Theorem 1.2 counts peaks and ties. The refinement must distinguish
the descent introduced at a nonempty left gap from the ascent at
a nonempty right gap and retain both orientations of a one-sided
insertion at an old peak. [Preregistration #33629](https://github.com/the-omega-institute/trureturing/issues/33629)

## Route

For 2 ≤ m ≤ n, isolate the words with exactly r letters equal to m.
When r is positive, the first such letter in sorted order has rank
n − r + 1, so r ≤ n − m + 1. Deleting the copies of m gives a word
of length ℓ = n − r at bound m − 1 and one ordered list of ℓ + 1 gap
sizes summing to r. Inserting the copies according to that list
recovers the original word.

For a retained word with p peaks, k ties and d descents, use

```text
T = z/(1 − uz)               S = tz + uz²/(1 − uz)
L = 1 + vT                   R = 1 + T
A = 1 + vS                   D = v + vS
C = u + vS                   B = tv + v(1 + v)S + v²S²
I(ℓ,r)(t^p u^k v^d) = [z^r] L R A^(ℓ−1−d−k−p) D^(d−p) C^k B^p
G(n,1) = u^(n−1)
G(n,m) = G(n,m−1) + sum_{r=1}^{n−m+1} I(n−r,r)(G(n−r,m−1)).
```

L and R represent the ordered endpoints. A, D and C represent
unpaired interior ascents, descents and ties. Each old peak uses one
ascent and one descent and gives a disjoint block B. The terms of B
correspond to occupying neither, exactly one, or both of its gaps.
Extend I additively over the polynomial with its natural coefficients.

At v = 1 the bivariate factors become E = 1 + T, A = 1 + S,
C = u + S, and B = A² + t − 1, as in (10). The bivariate operator
on F extracts the coefficient of z^r in
E² A^(ℓ−1) F(B/A²,C/A), as in (11). Both 1 − uz and A are formal
power-series units. Applied to the enumerator, this gives (2) and
the bound-one value gives (3).

## Falsifier

A disagreement of any coefficient with literal bounded parking
words, or a disagreement at v = 1 with equations (2), (3), (10)
or (11), falsifies the corresponding equality.

## Evidence

- Exact fiber decomposition in
  `D5/S3/Combinatorics/Parking/MaximumLetterGaps.parkingGapEquiv`
  and `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.coefficient_fiber`.
- Ordered local coefficient formula in
  `D5/S3/Combinatorics/Parking/DescentGapKernel.closedKernel_coeff`.
- Insertion operator on monomials in
  `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.insertionOperator_monomial`.
- Initial values, trivariate recurrence and bivariate specialization in
  `D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence.result`.

## Triage

### What the settlement shows

The coefficient formula applies to every nonempty retained word with
letters below the inserted maximum, even when the retained word is
outside the parking family. The parking condition determines which
retained words and insertion sizes contribute. The local series proof
works over a commutative semiring, and the specialization to the paper's
unit formulas works over a commutative ring.

## ASSUMED-UNVERIFIED

Publication priority beyond the scope of the version and literature checks
in the preregistration remains unverified.
