---
slug: olairez-2026-dihedral-permutohedron-lattice-points
bibkey: olairez2026dihedralpermutohedron
doi: 10.48550/arXiv.2610.28672
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.latticePointCount_terminalSum
---

# Olairez Question 6.1 on lattice points of the dihedral permutohedron

## Problem

Colin Olairez, *Triangulation, Volume, and Symmetries of a Dihedral Group
Analogue of the Permutohedron*, arXiv:2610.28672v2, §6, printed p. 21,
asks:

> Can we describe the number of lattice points or the Ehrhart polynomial of the dihedral permutohedron?

For every natural n ≥ 3 and k ≥ 0, let Qₙ be the real convex hull of the
orbit of (1, 2, …, n)ᵀ under the permutation matrices of Eq. (2).
Count kQₙ ∩ ℤⁿ using the original integer-coordinate lattice.
[Question 6.1](https://arxiv.org/html/2610.28672v2#S6.Thmquestion1)

## Motivation

A uniform count gives the number of lattice points in Qₙ at k = 1
and in every integral dilation. The centered real wrap model alone
does not specify the integral lattice in the source coordinates.
The related affine-symmetry problem is Question 6.2.

## Gap

The Tier 1 preregistration examined arXiv v1 and v2, OpenAlex citations,
dihedral matrix polytopes, and cycle and generalized symmetric edge
polytopes. It found no published count in the source lattice within
that search. Some citation and closed-issue searches had access limits.
The uniform recurrence, quantifiers and stopping rule were preregistered
in [#33483](https://github.com/the-omega-institute/trureturing/issues/33483).

## Route

Use residue indices i = 0, …, n−1, with source label n at residue zero.
Set B = nk, S = n(n+1)/2 and T = n(n−1)/2. The cyclic difference
dᵢ = xᵢ₊₁ − xᵢ has sum zero and weighted sum W(d) = nx₀ − ∑ᵢxᵢ.
Its image of the plane ∑ᵢxᵢ = kS is the integral lattice coset
W(d) ≡ −kS modulo n. The residue is n/2 for even n and odd k,
and zero otherwise.

The frozen source-coordinate conjugacy and signed wrap hull criterion
identify feasible differences by the existence of a translate z = d + t1
with ∑ᵢ|zᵢ| ≤ B. For integral d, a feasible integral t exists whenever
a feasible real t exists. For the least integral t, |t| ≤ k and, with
a = ∑ᵢ|zᵢ| and p = #{i : zᵢ > 0}, the predecessor condition is
B + 2p < a + n.

Let Dᵢ(s,r,a,p) be the prefix count of coordinate sum s, weighted
residue r modulo n, absolute sum a, and p positive coordinates.
Start with D₀(0,0,0,0) = 1 and zero for all other states. For each
integer v with |v| ≤ B−a, add Dᵢ(s,r,a,p) to
Dᵢ₊₁(s+v, r+iv mod n, a+|v|, p+[v>0]).
The exact count E(n,k) is the sum of Dₙ(nt,Tt−kS mod n,a,p) over
integer |t| ≤ k, natural a ≤ B, p ≤ n and B+2p < a+n.
The least translate and the inverse cyclic difference recover a unique
source point from each terminal prefix.

## Falsifier

A source point missed by the coset or terminal filter, two terminal
prefixes recovering the same source point, or a discrepancy at any
n ≥ 3 and k ≥ 0 would invalidate the claimed count. The parity-sensitive
coset and k = 0 are included in the quantified target.

## Evidence

`OlairezQ62.source_coordinate_conjugacy` supplies the existing
original-coordinate bridge. `OlairezWrapHull.scaled_wrap_hull_iff`
establishes the absolute-sum criterion for positive n and all natural k.
`OlairezCount.latticePointCount_terminalSum` proves
Finite(SourcePoints n k) ∧ Nat.card(SourcePoints n k) = terminalSum n k
for every natural n ≥ 3 and k ≥ 0.
`OlairezCount.fourOneInput` names the pair (4, 1). The anonymous Lean
application uses the uniform cardinality theorem and the generic
recurrence identity, with kernel evaluation of the terminal filter, to
check the original source count of 22 on that input. The declaration
inventory contains the input definition and the uniform theorem. The
closed evaluation has no separate retained theorem. At k = 0 the
original hull dilates to the singleton origin, so the uniform equality
gives terminalSum n 0 = 1 for every n ≥ 3. The exact Lean check verifies
both equalities at zero dilation. The three named theorems above use
Classical.choice, Quot.sound and propext in the pinned Mathlib build.
The named input has an empty axiom closure.

## Triage

### What the settlement shows

**Proved.** The lattice-point alternative is solved for every n ≥ 3
and every integral dilation k ≥ 0. The characteristic recurrence is
a finite sum of prefix multiplicities over one representative per
feasible cyclic difference. The residue condition retains the
dilation-dependent source lattice, including even n and odd k.

**Checked application.** At `fourOneInput = (4, 1)` the original
source count is 22 by the uniform theorem and the computed recurrence.
At zero dilation the count is one for every n ≥ 3 since the dilation
is the singleton at the origin.

**Open here.** An explicit coefficient formula for the Ehrhart
polynomial remains open. Question 6.3, the arbitrary-basepoint
construction, is also outside this scope.

## ASSUMED-UNVERIFIED

The bounded literature search in #33483 found no prior source-lattice
count. Global priority remains unverified. The current exact replay
does not resolve the historical initial 45-minute probe event of
2026-11-23, whose timed session-bound compiler receipt is missing.
