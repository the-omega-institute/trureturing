---
slug: oeis-a178294-four-grid-collinear-triples
bibkey: mathar2010a178294
doi: null
url: https://oeis.org/A178294
triage: theorem
motivation_gids:
  - D5/S3/Arith/Lattices/FourGridCollinearTriples
---

# Collinear triples in the four-point grid

## Problem

OEIS A178294 records:

> %N A178294 Number of collinear point triples in a 4 X 4 X 4 X... n-dimensional cubic grid.

> %A A178294 _R. H. Hardin_, suggested by R. J. Mathar in the Sequence Fans Mailing List, May 24 2010

> %F A178294 Conjecture: a(n) = 8^n/2-3*4^n/2+6^n. a(n) = +18*a(n-1) -104*a(n-2) +192*a(n-3). G.f.: 4*x*(-1+7*x)/((6*x-1)*(8*x-1)*(4*x-1)). - _R. J. Mathar_, May 24 2010

The recurrence and generating function on the FORMULA line are consequences
of the displayed closed form, rather than separate targets here.

## Motivation

The FORMULA has remained explicitly labelled a conjecture since 2010. The
target is the full count for every dimension, with the OEIS object represented
as unordered three-element subsets of the four-point Cartesian grid.

## Gap

On 2026-09-13 the preregistration search checked the current OEIS entry and
revision history, Mathar's attached `a178294.pdf`, exact A-number and exact-title
searches on arXiv, the MathOverflow Stack Exchange API, and Crossref. A proof or
refutation was not found in the checked surfaces. OpenAlex could not be checked
because its daily quota was exhausted, GitHub authenticated code search was not
checked, and the MathOverflow web interface was blocked by Cloudflare. This is
a bounded search result, not an exhaustive literature or priority claim.

## Route

The private equivalence `geometricCodeEquiv` classifies every marked collinear
triple as either an oriented arithmetic progression or an extreme-line code.
In the first family, same-parity endpoints have an integral midpoint; the
private `apEndpointEquiv` supplies the bijection used by
`oriented_arithmetic_progression_count`. In the second family, endpoint pairs
are coordinatewise equal or extreme; `endpoint_pair_counts` counts them using
the private `coordinatePairsEquiv` and `diagonalCoordinatePairsEquiv`.
`Fintype.card_congr` transfers the classification to cardinalities, the two
counts rewrite the result, and `omega` proves the division-free identity.

## Falsifier

A dimension `d` for which the filtered `powersetCard 3` count differs from
`(8^d + 2*6^d - 3*4^d)/2` would refute the claim. Such a witness could arise
from a missed collinear triple, a non-collinear triple admitted by the minor
equations, or a failure of the geometric-code classification. The finite
enumerations below are supporting checks and do not replace the universal
proof.

## Evidence

- Lean module: `D5/S3/Arith/Lattices/FourGridCollinearTriples.lean`.
- Theorems: `endpoint_pair_counts`,
  `oriented_arithmetic_progression_count`, and `mathar_collinear_triples`.
- Public definitions: `GridPoint`, `Collinear`, `IsCollinearTriple`,
  `matharCount`, `SameParity`, `EqualOrExtreme`, `CoordinatePairs`,
  `DistinctCoordinatePairs`, `midpointCoordinate`, `midpoint`, and
  `OrientedArithmeticProgression`.
- The canonical report gives each theorem exactly the std3 axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- The orchestrator independently enumerated dimensions 0 through 3 and found
  `0, 4, 44, 376`; the probe exhaustively checked through dimension 4 and also
  obtained `2960`.

## Triage

`theorem`. The formal result proves the conjectured closed form in the
division-free form
`2 * matharCount d = 8^d + 2*6^d - 3*4^d` for every natural `d`; the trailing
Lean example states the OEIS division form.

## ASSUMED-UNVERIFIED

The bounded literature result depends on the search surfaces and access
limitations listed under Gap. The attribution, revision date, and relationship
of Mathar's attachment to the conjectural calculation are source-level facts,
not kernel-checked claims. Exhaustive literature coverage, first-publication
priority, and the unchecked OpenAlex and GitHub surfaces remain unverified.
