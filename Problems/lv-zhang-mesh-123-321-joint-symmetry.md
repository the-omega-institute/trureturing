---
slug: lv-zhang-mesh-123-321-joint-symmetry
bibkey: lvzhang2025mesh
doi: 10.48550/arXiv.2501.00357
url: https://arxiv.org/abs/2501.00357v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/MeshPattern/MeshPatternS21.result
---

# Joint Symmetry of the Mesh Patterns 123 and 321 with Shading {0,1,2}² ∪ {(3,3)}

## Problem

Shuzhen Lv and Philip B. Zhang, *Joint Equidistributions of Mesh Patterns 123 and 321 with Symmetric and
Minus-Antipodal Shadings*, arXiv:2501.00357v3, Section 2.4, Conjecture 2 (printed page 9), pair S21: the mesh
patterns (123, R) and (321, R) are jointly equidistributed on Sₙ, where R = {0,1,2}² ∪ {(3,3)} as rendered in
the source's diagram.

An occurrence of (123, R) in π is a triple of positions with increasing values such that no other point of π lies
in a shaded cell; (321, R) is the same with decreasing values. Joint equidistribution means that, for all n, k
and l, the number of π ∈ Sₙ with k occurrences of (123, R) and l occurrences of (321, R) equals the number with l
and k.

## Motivation

The theorem `D5/S3/Combinatorics/MeshPattern/MeshPatternS21.result` establishes the statement for every n.

## Gap

Pre-registration issue 12358 records the literature screen: the source proves only Wilf-equivalence, and the
arXiv, GitHub and repository searches located no proof of the joint statement. This is a bounded negative
finding.

## Route

1. An occurrence is determined by its largest value m: it exists exactly when the origin-anchored rectangle Cₘ
   (positions at most n − m + 3, values at most m) contains exactly three points, including the point of row m and
   the point of column n − m + 3, and the order type of these three points decides between 123 and 321.
2. The rectangles Cₘ form a Ferrers shape. A seven-state involution acting inside the union of the rectangles that
   contain exactly three points preserves the number of points in every Cₘ and both incidences, and exchanges the
   increasing and decreasing order types in each rectangle with three points.
3. The involution therefore exchanges the two occurrence counts at every largest value simultaneously.

## Falsifier

The statement would fail if some occurrence were not captured by its rectangle, if the involution changed a
rectangle count or an incidence, or if it failed to be an involution.

## Evidence

The joint distributions are symmetric for every n ≤ 10; an independent referee implementation checked the
occurrence criterion, the rectangle reformulation and the involution on all 4,037,914 permutations with n ≤ 10.

## Triage

`theorem`; the statement is Conjecture 2 (pair S21) of arXiv:2501.00357v3 and is quantified over every n.

- Proved (formalized): the stronger simultaneous exchange of the occurrence indicators at every largest value,
  and hence the joint symmetry.
- Proved (paper argument, not formalized): the same exchange follows from Fomin growth diagrams on the Ferrers
  shape formed by the rectangles, with the cells outside the shape held fixed. Pair S22 follows from S21 by reverse
  and complement, as the source notes.
- Computed: the numbers of permutations avoiding both patterns are 1, 2, 4, 14, 70, 440, 3262, 27578, 260596 for
  n = 1, …, 9.
- Open: a formula for these numbers, and for the full joint distribution; no such formula is proved here.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv, GitHub and repository searches recorded above; the shading was read
from the rendered diagram of arXiv v3.
