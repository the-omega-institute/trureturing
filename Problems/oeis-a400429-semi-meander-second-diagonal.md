---
slug: oeis-a400429-semi-meander-second-diagonal
bibkey: hogan2026a400429
doi: null
url: https://oeis.org/A400429
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SemiMeanderSecondDiagonal.result
---

# OEIS A400429 second semi-meander diagonal

## Problem

OEIS A400429 revision 16 states verbatim: "Conjecture: D_2(n) =
(n^2 + 2*n + n mod 2 - 20)/2, for n >= 4." Its diagonal is
`D_j(n)=T(n,floor(n/2)-j+1)`, where `T(n,k)` counts one-loop semi-meanders
with `n` crossings and winding `2*(k-1)+(n mod 2)`. The source's equivalent
arch model fixes a lower rainbow pairing of `2*n` vertices and counts
noncrossing upper perfect matchings whose union with it is one loop. The
second diagonal has exactly `n-4` upper arches crossing the midpoint.

## Motivation

The entry still labels this all-order formula a conjecture. Issue #11034
registered the external open-problem settlement before the Lean proof probe;
the issue is a registration locator, not mathematical evidence.

## Gap

Di Francesco, Golinelli and Guitter (1996), Appendix D (D.9)-(D.14), give
a resummed small-`t` prediction whose second-diagonal coefficient is the same
polynomial. Their conclusion calls (D.14) a "purported re-summation". The
inspected argument does not establish all finite-`n` coefficient validity.
The formula is credited to that prediction; this result is an independent
proof, with no first-proof claim.

## Route

Index vertices from zero. A Lean `UpperMatching n` is the fixed-point-free
involution on `Fin (2*n)` for the upper arches. Its noncrossing condition
excludes `a<b<M(a)<M(b)`. The lower rainbow is `x.rev=2*n-1-x`.
`M.winding` counts left-half vertices `x<n` with `M(x)>=n`; this counts
each midpoint-crossing upper arch once. `M.oneLoop` says every two vertices
are connected by the reflexive transitive closure of upper and lower pairing
steps. Therefore the theorem's nested subtype counts precisely source
objects with winding `n-4` and one loop, for every natural `n>=4`.

The proof cuts both halves at the midpoint. Four vertices on each side
belong to non-crossing local pairs; the other `n-4` upper arches cross the
midpoint. A connected union with the lower rainbow forces the local pairing
types and their compatible cross-half connections. Their count gives
`(n^2+2*n+(n mod 2)-20)/2`, with natural division by two. At `n=4`, the
formula is `2`, and the source table has `T(4,1)=2`.

## Falsifier

A noncrossing upper matching with one-loop rainbow union and `n-4`
midpoint-crossing arches counted differently from the source's `D_2(n)`,
or any `n>=4` whose model count differs from the polynomial, would defeat
the claimed source bridge or formula respectively. Bounded table agreement
alone does not settle the unbounded claim.

## Evidence

The Lean model is in
`D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Model.lean`; its five ordered
`Stage1.lean` through `Stage5.lean` modules establish the cut classification,
connectivity and count. The short
`D5/S3/Combinatorics/SemiMeanderSecondDiagonal.lean` module states the exact
all-`n` `result`. The mathematical source mapping and theorem statement were
independently approved before this publication-artifact work. Source
attribution, the Scribe interpretation, deposit, independent publication
review and merge are separate from the kernel statement.

## Triage

Tier 1 external named conjecture (OEIS A400429, revision 16), registered in
issue #11034. `theorem`; resolution `proved`; admission basis
`open-problem-resolution`; `proof_shape: content`. The proof classifies the
local pairings and compatible cross-half connections on the live path.

## ASSUMED-UNVERIFIED

The literature check covers OEIS A400429 revision 16 and the cited 1996
arXiv PDF, including Appendix D and its conclusion. It is not an exhaustive
search of later literature or a priority certification. The separate
`declared_validated` escape audit remains unfinished (issue #11180).
