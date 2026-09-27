---
slug: oeis-a400216-a400218-tetrahelix-generating-functions
bibkey: kagey2026a400216tetrahelix
doi: null
url: https://oeis.org/A400216
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions
---

# Three tetrahelix coordinate generating functions

## Problem

OEIS A400216, A400217 and A400218, Peter Kagey (2026), conjecture the
coordinate generating functions of one Boerdijk-Coxeter tetrahelix. The
ordered initial vertices are (-1,-1,-1), (-1,1,1), (1,-1,1), (1,1,-1).
At each step the oldest vertex is reflected across the face through the next
three. The coordinates are scaled by 1 through index 3 and by 3^(n-3)
thereafter. In the order x, y, z, the proposed series are

- (54t^6-84t^5-66t^4+23t^3+9t^2+t-1)/((3t-1)^2(9t^2+4t+1));
- (-54t^6+84t^5-90t^4+15t^3+3t^2+3t-1)/((3t-1)^2(9t^2+4t+1));
- (18t^5+26t^4-24t^3-5t^2+1)/(27t^3+3t^2-t-1).

The denominators are units in rational formal power series, with respective
constant coefficients 1, 1 and -1. Preregistration is issue #10182.

## Motivation

The three entries describe coordinates of one geometrically specified
tetrahelix. Their common recurrence makes them one connected problem, not
three independent resolutions. A finite match with the printed terms would
not establish any of the conjectured generating functions.

## Gap

The September 26, 2026 OEIS records still label all three formulas
conjectured. Exact A-number searches in D5, pinned Mathlib and external Lean
searches found no older exact proof. The full 15-page preprint
arXiv:1302.1174 studies face reflection followed by rotation for modified
periodic helices; it does not state these scaled coordinate series.

## Route

The D5 result constructs vertices from the ordered initial tetrahedron by
the order-four reflection recurrence. At every step it proves squared edge
length 8, a nonzero face normal, noncollinearity of the face vertices, their
containment in the plane perpendicular to that normal, and the face centroid
as midpoint of the old and new vertices. It proves all three generating
functions as equalities of rational formal power series, hence at every
natural coefficient index. The scaled order-four tail and finite numerator
correction yield the x and y fractions; cancellation of a nonzero factor
yields the z fraction.

The OEIS records also characterize the ordered choice by asymptotically
maximizing x and then y among 24 symmetries. For any coordinate and ordering,
reflection gives u_(n+4) = (2/3)(u_(n+1)+u_(n+2)+u_(n+3)) - u_n. Thus

`U(t) = P(t)/((1-t)^2(1+4t/3+t^2))`, where
`P(t) = u0 + (u1-2u0/3)t + (u2-2(u0+u1)/3)t^2
       + (u3-2(u0+u1+u2)/3)t^3`.

The characteristic roots are the double root 1 and the distinct roots
(-2 +/- i sqrt(5))/3, both of modulus one. Hence
`u_n = beta*n + O(1)` with
`beta = P(1)/(10/3) = (-3u0-u1+u2+3u3)/10`.
Let A, B, C, D be the four initial vertices in the order above. The weights
(-3,-1,1,3) maximize beta_x = 4/5 exactly when A,B (x = -1) occupy positions
0,1 and C,D (x = 1) occupy positions 2,3. Those four orders have the same
entire x sequence; every other order eventually has a smaller x coordinate.
The OEIS scaling factor is common and positive, so it preserves comparisons.
For ABCD, ABDC, BACD and BADC, the respective y slopes are 2/5, 0, 0 and
-2/5. Thus ABCD uniquely maximizes y among the x ties. This asymptotic
comparison is a separate mathematical check, not part of the Lean theorem.

## Falsifier

An exact mismatch at any coefficient of one of the three claimed rational
series, or a failure of face reflection for the ordered vertex recurrence,
would refute the corresponding claim. Matching finitely many printed terms
alone cannot settle the all-index identities.

## Evidence

The public Lean result has only propext, Classical.choice and Quot.sound in
its axiom closure, with no sorry or added axiom. Its proof uses the exact
first seven vertices for the numerator correction, including scaled triples
(5,5,5), (31,1,1) and (83,77,-13). Direct rational iteration also matches
the remaining printed OEIS vertices. The bounded source search and full
arXiv preprint check are described under Gap.

## Triage

`theorem`. The single public result resolves the three coordinate formulas
for the one specified tetrahelix. Preregistration is issue #10182.

## ASSUMED-UNVERIFIED

The literature search is bounded and does not establish global publication
priority. OEIS provenance and the asymptotic comparison of all 24 ordered
choices are not Lean-kernel statements. The four-slot escape audit remains
unfinished under issue #10201.
