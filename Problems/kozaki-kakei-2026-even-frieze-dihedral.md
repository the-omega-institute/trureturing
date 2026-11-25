---
slug: kozaki-kakei-2026-even-frieze-dihedral
bibkey: kozakikakei2026coxeterfriezes
doi: 10.48550/arXiv.2611.25785
url: https://arxiv.org/abs/2611.25785v1
triage: theorem
motivation_gids:
  - D5/S3/Geometry/KozakiKakeiConjecture13.conjecture_13
---

# Kozaki–Kakei Conjecture 13 on even frieze symmetry

## Problem

Yuta Kozaki and Saburo Kakei, *Coxeter Group Symmetries of Frieze Patterns*,
arXiv:2611.25785v1, §3, printed p. 9, Conjecture 13, state:

> If $m \ne 3$, the symmetry group of $\widehat{\widehat{\mathcal{M}\,}}_{2m}$ coincides with the dihedral group $\mathcal{D}_{2m}$.

For every natural $m\ge2$ with $m\ne3$, take all $2\times2m$ matrices over
$\mathbb C(X)$ with all minors on distinct columns nonzero. A normalized matrix
has first three columns $(0,-1),(1,0),(1,1)$ and its consecutive minors and
closing minor $D_{1,2m}$ equal one. In the ambient symmetric group, a permutation
is allowable when for each normalized input its column reorder has a unique
normalized representative under invertible left multiplication and invertible right
diagonal scaling. The conjecture identifies these permutations with the rotations
and reflections of the labeled cycle.
[Primary edition](https://arxiv.org/html/2611.25785v1#Thmproposition13)

## Motivation

The dihedral permutations already act by reordering and normalizing. The question
asks whether the same construction extends to any other permutations on the
whole normalized locus.

## Gap

The bounded search found precedents for even-order normalization, the cyclic
multi-ratio and the exceptional six-point symmetry. Within the inspected scope
it found no classification of all column reorderings in the entire stated size range.
[Library note](../Library/FiniteGeometry/kozakikakei2026coxeterfriezes.md) ·
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/32810)

## Route

The normal form exists uniquely on the admissible level equating
$D_{2,3}D_{4,5}\cdots D_{2m-2,2m-1}D_{1,2m}$ with
$D_{1,2}D_{3,4}\cdots D_{2m-1,2m}$. Reordering transports matrix equivalence.
Thus the allowable permutations are exactly the universal preservers of this
equality. A dihedral permutation preserves or exchanges the matchings and
introduces a common orientation factor.

For the reverse implication, the affine constant matrices with distinct complex
coordinates give the zero locus of the signed matching polynomial. Isolate the
first variable. Relative primeness of the two coefficients and nonvanishing of
the collision factors allow specialization at the linear root and then give
polynomial divisibility. Total degree makes the quotient a nonzero scalar.

For $m\ge4$, count nonzero signed evaluations on Boolean assignments with both
specified columns true. Each adjacent pair has exactly $2^{m-2}$ such
assignments. For a nonedge, each individual matching admits $2^{m-2}$ cuts and
at most one cut is common to both. Even after removing that common cut from
both counts, the count is strictly greater than $2^{m-2}$. For $m=2$, the signed
quadratic on two-column indicators is one on edges and minus two on diagonals.
Either argument forces an allowable permutation to preserve cycle adjacency,
which determines its start column and orientation.

## Falsifier

An in-range nondihedral permutation preserving the literal level on every
admissible matrix would contradict necessity. A single admissible level matrix
whose dihedral reorder violates the equality would contradict sufficiency.
The matrices and permutations in both tests use the source closing orientation.

## Evidence

The exact Lean endpoint is
`D5/S3/Geometry/KozakiKakeiConjecture13.conjecture_13`.
Its standard axiom closure is `Classical.choice`, `Quot.sound` and `propext`.
The independently qualified literature scope and its access limits are recorded
with the primary edition. [Library note](../Library/FiniteGeometry/kozakikakei2026coxeterfriezes.md)

## Triage

`theorem`. This is the in-range classification asked for by the published conjecture.

### What the settlement shows

**Formally proved** by `D5/S3/Geometry/KozakiKakeiConjecture13.conjecture_13`.
Even though the hypothesis of necessity concerns every rational-function
matrix, testing the distinct-coordinate affine constant matrices suffices.
A scalar symmetry then preserves a signed support invariant that reconstructs
the cycle for every $m\ge4$. The proof treats $m=2$ by signed evaluations
on pairs of columns.

**Source-attested.** Equation (54) transports the maps to complete Coxeter
friezes via $\check{\rho}(\sigma,c)=\alpha^{-1}\circ\rho(\sigma,c)\circ\alpha$
on $\mathcal{CCF}_{2m}$, where $\alpha$ is the bijection with the
single-normalized matrix space. In equation (45),
$\rho(\sigma,c)=\eta(c)\circ\rho(\sigma)\circ p$,
where $p$ sends a single-normalized matrix to its double-normalized form and
$\eta(c)$ restores the scaling parameter. In the stated range the Lean
classification determines the column-permutation input $\sigma$ on this
double-normalized locus. The transport through $\alpha$ and the scaling
parameter are supplied by the paper.
[Equation (45)](https://arxiv.org/html/2611.25785v1#S3.E45) ·
[Equation (54)](https://arxiv.org/html/2611.25785v1#S3.E54)

**Source-attested.** Proposition 11 gives six-column multi-ratio preservation
for permutations that preserve opposite pairs. The paper uses this to obtain
its $W(B_3)$ action at $m=3$, outside the range of the Lean classification.
[Proposition 11](https://arxiv.org/html/2611.25785v1#Thmproposition11)

**Computed in the source.** The authors report computer checks of Conjecture 13
for $m=2,4,5,6$. Example 14 computes instances of the transported action at
six columns.
[Conjecture 13](https://arxiv.org/html/2611.25785v1#Thmproposition13) ·
[Example 14](https://arxiv.org/html/2611.25785v1#Thmproposition14)

**Open within this resolution.** Remark 15 asks for a corresponding symmetry classification for
$SL_k$ friezes using $k\times n$ matrices or $\mathrm{Gr}(k,n)$. The signed
pair-minor argument here settles the stated rank-two level-one case.
[Remark 15](https://arxiv.org/html/2611.25785v1#Thmproposition15)

## ASSUMED-UNVERIFIED

Priority beyond the bounded qualification search remains unverified.
