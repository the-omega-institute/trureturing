---
slug: oeis-a077864-trinomial-odd-diagonal-rational-series
bibkey: schulte2015a077864
doi: null
url: https://oeis.org/A077864
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries
---

# The trinomial odd diagonal of OEIS A077864

## Problem

> Expansion of (1-x)^(-1)/(1-x-2*x^2-x^3).

> Triangle of trinomial coefficients T(n,k) (n >= 0, 0 <= k <= 2*n), read by rows: n-th row is obtained by expanding (1 + x + x^2)^n.

> a(0)=1, a(1)=2, a(2)=5, a(3)=11, a(n)=2*a(n-1)+a(n-2)-a(n-3)-a(n-4) for n>3. - _Philippe Deléham_, Oct 25 2006

> Conjecture: a(n) = Sum_{j=0..n/2} A027907(n+1-j,2*j+1), n >= 0. - _Werner Schulte_, Sep 29 2015

## Motivation

OEIS A077864 attributes the order-four recurrence to Philippe Deléham and the
odd trinomial-diagonal formula to Werner Schulte. The formal target keeps the
entry's generating-function definition and expresses the proposed identity for
every natural index. The coefficient sequence is treated as rational-valued,
matching the power-series construction in Lean.

## Gap

The preregistration search surfaces dated 2026-09-13 were the current OEIS
entry and public history, the arXiv API (`A077864 OR A027907`, 0), the
MathOverflow API (0), Crossref (0), GitHub repository search (0; code search
returned 401), and OpenAlex (429). A separate Google Scholar search found only
a biological false positive and no joint hit. A proof was not found in the
checked surfaces. This bounded search does not establish exhaustive coverage
or publication priority.

## Route

For the trinomial triangle, write `G` for the inverse of
`1 - X^2(1+X+X^2)`. Finite-support truncation of the substituted geometric
powers gives the coefficient at degree `2n+3` as the finite sum over the
reflected exponents. Reindexing by reflection and bounding the polynomial
degree removes the zero tail and leaves `j <= floor(n/2)`.

For the rational series, the two reflected inverse equations for
`1-X^2-X^3-X^4` and `1-X^2+X^3-X^4`, together with their denominator product,
give the odd-part identity
`2·X^3·(expand 2 G') = G - rescale(-1) G`. Extracting the coefficient at
`2n+3` identifies the rational-series coefficient with the odd diagonal sum.

## Falsifier

A natural index `n` with a coefficient mismatch between `a(n)` and
`Sum_{j=0..n/2} A027907(n+1-j,2*j+1)` would falsify the conjecture. A mismatch
in the finite-support coefficient identity or in the reflected inverse
equations would also invalidate the route. The exact checks through `n < 60`
and `n <= 99` are supporting computations, not substitutes for the universal
proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.lean`.
- Main theorems: `odd_trinomial_diagonal_coeff` and `schulte_a077864`.
- Public definitions: `trinomial`, `generatingSeries`, and `a`.
- Both theorems have the standard three axioms (`propext`, `Classical.choice`, `Quot.sound`).
- The orchestrator's exact check found no mismatch for `n < 60`.
- The probe check found no mismatch for `n <= 99` and used SymPy for exact
  simplification of the odd-part generating function.

## Triage

`theorem`. The Lean proof establishes the universal odd-diagonal identity and
the resulting Schulte formula for the rational generating series.

## ASSUMED-UNVERIFIED

The OEIS quotations, author attributions, dates, and the identification of the
two entries were supplied by the preregistration and literature-search seats.
The search scope is the dated set of surfaces listed above; no exhaustive
literature or priority claim follows. The finite exact checks and SymPy
simplification are supporting evidence supplied by the orchestrator and probe
seat. The translation from the OEIS notation to the Lean expressions is not
itself a kernel-checked bibliographic fact.
