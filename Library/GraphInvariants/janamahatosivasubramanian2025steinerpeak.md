---
bibkey: janamahatosivasubramanian2025steinerpeak
authors: S. Jana; I. Mahato; S. Sivasubramanian
year: 2025
title: Unimodality and peak location of the characteristic polynomials of two distance matrices of trees
doi: 10.1007/s40314-025-03163-5
url: https://arxiv.org/abs/2407.03309v1
claim: "Conjecture 29 places the largest nonleading coefficient magnitude of the path's principal 2-Steiner distance characteristic polynomial at n−1 for every n>5."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1007/s40314-025-03163-5

Source: https://arxiv.org/abs/2407.03309v1

Computational and Applied Mathematics 44, article 223 (2025). Page numbers
refer to arXiv:2407.03309v1.

## Source definitions

Page 3 states:

> the entry of 𝔇_2(T) corresponding to the row {i,j} and column {k,l} is the minimum number of edges among all connected subtrees of T whose vertex set contains the four vertices i, j, k and l.

Remark 23, page 14, states:

> Let P_n be the path on n vertices with edges e_i = {i, i+1} for i = 1, …, n−1. Let B = (e_1, f_1, e_2, f_2, …, e_{n−2}, f_{n−2}, e_{n−1}) be the ordered basis for the row space of 𝔇_2(P_n) where f_j = {j, j+2}, for j = 1, …, n−2.

The same page states:

> We denote by 𝔇_{P_n} the matrix 𝔇_2(P_n)[B, B], that is, 𝔇_{P_n} := 𝔇_2(P_n)[B, B].

On the path, connected subtrees are intervals [a,b] with b−a edges.
Zero-based even and odd indices enumerate the edge pairs and the length-two
pairs respectively. The matrix entries are integer casts of these distances.

## Conjecture 29

Page 18 states:

> For a path P_n on n > 5 vertices, if CharPoly_{𝔇_{P_n}}(x) = Σ_{i=0}^{2n−3} a_i x^i and |a_ℓ| = max{|a_0|, |a_1|, …, |a_{2n−4}|}, then ℓ = n − 1.

The leading coefficient is excluded from the maximum. The source's small
examples cover 6≤n≤14; its upper bound is ℓ≤⌊7n/5⌋.

## Refutation and scope

For n=16, the principal matrix has order 29. Its characteristic polynomial
has |a_15|=939602445008 and |a_16|=956326515118, with index 16 attaining
the maximum over indices 0 through 28. Thus the asserted index 15 fails.
The source upper bound gives 22 at n=16 and is consistent with this value.
The refutation leaves the separate trace identity and Conjecture 30 intact.
No peak formula for unbounded n follows.

The literature screen in issue #19152 found no settlement of Conjecture 29
and identified a posted solution of Conjecture 30. Literature completeness
and correspondence with the journal full text are ASSUMED-UNVERIFIED.
