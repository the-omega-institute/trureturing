---
bibkey: ulfarsson2024bisc
authors: Henning Ulfarsson
year: 2024
title: "BiSC: An algorithm for discovering generalized permutation patterns"
doi: 10.48550/arXiv.2411.17778
url: https://arxiv.org/abs/2411.17778v1
claim: "Conjecture 2.4.2: every mesh-pattern basis of the even permutations consists exactly of fully shaded odd permutations."
strata_touched:
  - D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis
license: citation-only
triage: anchor
---

# The mesh-pattern basis of the even permutations

## Verified locator

DOI: 10.48550/arXiv.2411.17778

Source: https://arxiv.org/abs/2411.17778v1

Conjecture 2.4.2 is on page 8. The definition of a basis is in Section 2,
page 2; the mesh-pattern interpretation is in Section 2, page 3.

## Source statements

“Given a set of permutations A, we call a set of patterns P a basis for A if
A = Av(P), and no subset of P has this property.” (Section 2, page 2.)

“We let S denote the set of all permutations and Av(P) denote the permutations
that avoid all the patterns in a set P.” (Basic definitions, page 2.)

“This inspired West [Wes90] to define barred patterns, but we will use the more
expressive mesh patterns of Brändén and Claesson [BC11], which allow us to
forbid letters from occupying certain regions in a pattern.” (Section 2, page 3.)

“Let A be the union of the alternating subgroups, and let P be a basis of
patterns such that A = Av(P). Then
P = {(p, {0, …, n} × {0, …, n}) : p ∈ S_n ∖ A for some n}.”
(Conjecture 2.4.2, page 8.)

## Mathematical encoding

A mesh pattern has length `k`, a permutation `p : Equiv.Perm (Fin k)`, and a
set `R : Set (Fin (k + 1) × Fin (k + 1))` of shaded cells. The occurrence
predicate selects positions by an order embedding, preserves relative order of
values, and forbids every unselected point from lying in a shaded cell. A cell's
coordinates count selected positions to its left and selected values below it.
All permutation lengths, including zero, are retained. Evenness is
`Equiv.Perm.sign p = 1`, and full shading is `R = Set.univ`.

The companion theorem proves Conjecture 2.4.2. Inserting two points in one
unshaded cell preserves the occurrence and admits both parities. Full shading
forces every point to be selected, so a fully shaded pattern occurs only in its
underlying permutation. These two facts determine the forbidden set from its
avoidance class. The proof uses the equality of avoidance classes without using
the minimality clause in the definition of a basis.

## Scope

Conjecture 2.4.1 about the dihedral subgroups is outside this result. No theorem
for other permutation sets is asserted. Literature completeness beyond the
sources recorded in issue #19120 is ASSUMED-UNVERIFIED; that issue records the
citation-search scope and Semantic Scholar's HTTP 429 response.
