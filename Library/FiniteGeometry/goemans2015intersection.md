---
bibkey: goemans2015intersection
authors: Michel X. Goemans
year: 2015
title: Lecture notes on matroid intersection
doi: null
url: https://math.mit.edu/~goemans/18433S15/matroid-intersect-notes.pdf
claim: Every extreme point of the actual nonnegative rank-inequality intersection of two finite matroids is a zero-one vector.
strata_touched:
  - D5/S3/Combinatorics/Matroids/FiniteIntersectionPolytope
license: citation-only
triage: anchor
---

# Finite matroid intersection rank regions

## Verified locator

Michel X. Goemans, MIT 18.433, *6. Lecture notes on matroid intersection*,
version April 8, 2015:
https://math.mit.edu/~goemans/18433S15/matroid-intersect-notes.pdf .
Theorem 6.6 and its proof, printed and PDF pages 7–8, define the real region
by nonnegativity and both complete subset-rank inequality families. The proof
first establishes that every extreme point is integral and then identifies the
region with the convex hull of common-independent incidence vectors. The Lean
result formalizes the zero-one extreme-point conclusion for the inequality
region itself; it does not assume or separately prove that hull equality.

The supporting *5. Matroid optimization* notes are at
https://math.mit.edu/~goemans/18433S15/matroid-notes.pdf . Lemma 5.5 on page 10
proves that the tight sets are closed under union and intersection. Theorem
5.6 and its proof on page 11 replace the tight equations of a face by a
maximal chain; the proof gives equality of the relevant incidence spans.
The intersection notes' reference to Theorem 4.6 points to this result,
numbered Theorem 5.6 in the linked version.

For two separately laminar families, the incidence-matrix total-unimodularity
statement is Claim 3 on printed pages 12-2–12-3, PDF pages 2–3, of MIT 18.438,
Lecture 12, October 27, 2009, scribe Chung Chan:
https://math.mit.edu/~goemans/18438F09/lec12.pdf . Chains are a special case.
This statement concerns selected laminar rows, not all subset-rank rows.
The Lean proof instead identifies the equivalent disjoint-layer rows directly
with a signed-incidence submatrix and invokes the existing native TU theorem.

The finite linear-inequality background is also explicit in Goemans's
*Polyhedral combinatorics* notes,
https://math.mit.edu/~goemans/18433S15/polyhedral.pdf : Theorem 3.6, page 7,
characterizes a vertex by uniqueness of its tight equations; Theorem 3.12,
page 14, gives integral vertices for a TU inequality matrix with integral
right-hand side. The Lean argument reuses the native active-kernel theorem
and the native integer inner inverse, with no full-rank or nonempty-matrix
premise.

The result is classical. The ground type may be empty; loops, rank zero,
unequal ranks and nonrepresentable matroids remain in scope. No novelty,
weighted-optimization or fractional-decomposition theorem is claimed.
These documents are cited for mathematics only. No PDF or externally authored
Lean code is redistributed, and no code-port licence is asserted for them.
