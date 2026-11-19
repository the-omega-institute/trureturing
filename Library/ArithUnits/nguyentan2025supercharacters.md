---
bibkey: nguyentan2025supercharacters
authors: Tung T. Nguyen, Nguyen Duy Tân
year: 2025
title: Supercharacters of finite abelian groups and applications to spectra of U-unitary Cayley graphs
doi: 10.48550/arXiv.2508.10348
url: https://arxiv.org/abs/2508.10348v1
claim: Question 4.17 asks whether a connected and anti-connected U-unitary Cayley graph over a finite commutative Frobenius ring is prime exactly when zero is not an adjacency eigenvalue.
strata_touched:
  - D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum
license: citation-only
triage: anchor
---

# Supercharacters and unitary Cayley graphs

## Verified locator

DOI: 10.48550/arXiv.2508.10348

Source: https://arxiv.org/abs/2508.10348v1

The source is version 1, Section 4.3, Question 4.17, page 19.

## Source statements

Question 4.17, page 19:

> Suppose that Γ(R, U) is both connected and anti-connected. Is it true that Γ(R, U) is prime if and only if 0 is not an eigenvalue?

Section 3.1, page 7:

> Let R be a finite commutative ring and S be a symmetric subset of R

> we fix a subgroup U of R× such that −1 ∈ U (this will ensure that all relevant generating sets are symmetric).

Section 3.3, page 10:

> A subset X in a graph G is called a homogeneous set if every vertex in V(G) \ X is adjacent to either all or none of the vertices in X.

> A homogeneous set X with 2 ≤ |X| < |V(G)| is called non-trivial. The graph G is said to be prime if it does not contain any non-trivial homogeneous sets.

Section 4.1, page 12:

> being Frobenius means that R is a Z/n algebra equipped with a non-degenerate Z/n linear functional ψ : R → Z/n. Here, non-degenerate means that the kernel of ψ does not contain any non-zero ideal in R.

## Mathematical correspondence

The ring is a finite type carrying `CommRing`. A subgroup of `Units R`
contains minus one. `SimpleGraph.fromRel` symmetrizes the relation saying
that `a - b` is the value of a unit in the subgroup, and removes loops.
With minus-one membership this is the source's Cayley graph.
Anti-connectedness means connectedness of the graph complement.

Homogeneity gives two alternatives for each outside vertex: adjacency to
every member of the set, or adjacency to none. Primeness excludes a
homogeneous finset of cardinality at least two and smaller than the vertex
type. A zero adjacency eigenvalue is expressed by a nonzero complex
vector annihilated by `Matrix.mulVec`. This expression agrees with
`Module.End.HasEigenvalue` at zero for the adjacency linear map.

The counterexamples use `MonoidAlgebra (ZMod 2) G` with the subgroup of
basis units for finite commutative groups of even cardinality at least three.
Coefficient vectors give the binary Hamming graph. The cyclic specialization
uses `Multiplicative (ZMod d)` for even `d ≥ 4`. An isomorphism with the
polynomial quotient is not part of the formal statement.

## Scope

The failed implication is primeness implying absence of a zero eigenvalue.
The reverse direction in Proposition 4.16 and the source's structure results
is unaffected. The formal argument constructs a zero eigenvector and does
not assert a complete eigenbasis or its multiplicity.

The finite numerical experiment is in
`the-omega-institute/trureturing-experiments`, commit
`f7b6aa25309df5b390bb7bc5e9508beca82b63e8`, at
`docs/reports/nguyen-tan-2025-unitary-cayley-prime-zero-eigenvalue/check.py`,
SHA-256 `b999f68f21251f9c72f08a43ba1f5d04ea36da575a4d727cb4c6ddc69e4c10e2`.
Preregistration issue #20113 records exit code 0. Those numerical readings
are distinct from the Lean proof.

## Literature boundary

The literature screen in issue #20113 includes the repeated Question 2.20
in arXiv:2603.21239v1, the source comparison with arXiv:2401.06062v1,
and the screened arXiv:2607.00404v1 and arXiv:2609.30407v1.
Completeness of this literature screen is `ASSUMED-UNVERIFIED`.
