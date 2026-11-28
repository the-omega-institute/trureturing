---
bibkey: olairez2026dihedralpermutohedron
authors: Colin Olairez
year: 2026
title: Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron
doi: 10.48550/arXiv.2610.28672
url: https://arxiv.org/html/2610.28672v2#S6.Thmquestion2
claim: "Questions 6.1 and 6.2 ask for the lattice-point count or Ehrhart polynomial and for the full affine symmetry group of the dihedral permutohedron."
strata_touched:
  - D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount
  - D5/S3/Combinatorics/Geometry/Permutohedra/OlairezWrapHull
  - D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62
  - D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer
license: citation-only
triage: anchor
---

# Olairez on the dihedral permutohedron

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2610.28672
- URL (declared; Question 6.2): https://arxiv.org/html/2610.28672v2#S6.Thmquestion2
- URL (Question 6.1): https://arxiv.org/html/2610.28672v2#S6.Thmquestion1
- Version and location: arXiv:2610.28672v2, §6, printed p. 21, Questions 6.1 and 6.2.

Question 6.2 of arXiv:2610.28672v2, §6, p. 21 asks:

> What is the full group of affine symmetries for the dihedral permutohedron?

The source uses the permutation matrices in Eq. (2) acting on the
column vector `(1,…,n)`, and the two vertex families of Eqs. (5) and
(7). Matrix multiplication acts by the inverse index. The classification
uses all real affine bijections of the affine hull of that orbit.
Section 5 studies a particular lattice-preserving symmetry. Section 6
also asks about the construction with arbitrary basepoint.

## Lattice-point question

Question 6.1 of arXiv:2610.28672v2, §6, printed p. 21 asks:

> Can we describe the number of lattice points or the Ehrhart polynomial of the dihedral permutohedron?

The hull is the standard-basepoint orbit just described. A count in the
integer-coordinate lattice of its original realization answers the first
alternative. The count for every integral dilation includes the original
polytope at dilation one.

**Lattice-point alternative for n ≥ 3.** For every natural n ≥ 3 and k ≥ 0,
`OlairezCount.latticePointCount_terminalSum` proves finiteness of the
points of the original dilation kQₙ with integral coordinates and
equality of their cardinality with the terminal sum of a prefix
recurrence. It uses the source-coordinate conjugacy already formalized
for Question 6.2. The integral cyclic difference satisfies
W(d) ≡ −kn(n+1)/2 modulo n, including residue n/2 for even n and odd k.
Each feasible difference has exactly one least feasible integer translate.
The named input `OlairezCount.fourOneInput` supplies (n, k) = (4, 1).
An anonymous Lean application combines the uniform theorem with the
computed recurrence value to give 22 points in the original lattice.
At zero dilation the singleton origin gives one point for every n ≥ 3.
An explicit formula for the coefficients of the Ehrhart polynomial
remains open here.

At the two-label boundary of Eq. (2), the first matrix swaps the labels
and the second is the identity. Thus Q₂ is the segment from (1, 2) to
(2, 1), and kQ₂ has the lattice points (j, 3k − j) for integers
k ≤ j ≤ 2k. This gives k + 1 points for each natural k, a calculation
unverified in Lean here.
[Question 6.1](https://arxiv.org/html/2610.28672v2#S6.Thmquestion1)

## Related classifications

Voskresenskii and Klyachko, *Toroidal Fano Varieties and Root Systems*,
p. 238, give the odd-`n` symmetry classification for the normalized
del Pezzo model. [DOI](https://doi.org/10.1070/IM1985v024n02ABEH001229)

D’Alì, Juhnke-Kubitzke and Koch lift permutations of cycle edges with
possible column signs in the proof of Theorem 3.2. Theorem 4.3(v)
identifies the vertices of the normalized regular-matroid polytope.
For the cycle, the unique dependence among its consistently oriented
edges forces the signs of a lift to agree.
[Theorem 3.2](https://arxiv.org/html/2307.04933#S3.Thmtheorem2) ·
[Theorem 4.3](https://arxiv.org/html/2307.04933#S4.Thmtheorem3)

The literature search in #32848 reports the source title, author, arXiv
identifier and affine symmetry searches. In the sources examined there,
the normalized model gives the group calculation. The literal formula
`Δ(r_j-c)=1-n e_(1-j)` and the induced action on Olairez’s original
labels were not identified. The 1985 page attribution is recorded in
#32848 and in the source handoff. Direct access to that page remains
unverified. [Scope of the search](https://github.com/the-omega-institute/trureturing/issues/32848)
