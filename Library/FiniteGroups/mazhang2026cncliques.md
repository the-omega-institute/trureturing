---
bibkey: mazhang2026cncliques
authors: "Haobo Ma; Wenlin Zhang"
year: 2026
title: "Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem"
doi: "10.5281/zenodo.24398996"
url: "https://doi.org/10.5281/zenodo.24398996"
claim: "Proposition 7: a disjoint union H of k >= 1 cliques K_(s_i) on n = sum s_i vertices has E_CN(H) = 2 sum (s_i - 1)(s_i - 2) <= 2(n - 1)(n - 2), with equality iff k = 1, or k = 2 and s_1 = s_2 = 1."
strata_touched:
  - D5/S3/Combinatorics/Graph/CommonNeighborhood/CliqueUnionEnergy
  - D5/S3/Combinatorics/Graph/CommonNeighborhood/GroupCentralizerBound
  - D5/S3/Combinatorics/Graph/CommonNeighborhood/NeighbourhoodCliqueBound
  - D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound
license: citation-only
triage: anchor
---
<!-- GID: D5/L/FiniteGroups/mazhang2026cncliques -->
# Common-neighbourhood energy of a union of cliques

## Verified locator

The written proof is by **Haobo Ma and Wenlin Zhang**, version 2, exact-version DOI
https://doi.org/10.5281/zenodo.24398996, Proposition 7 in Section 4. The paper repository is
https://github.com/mathesis-papers/nath2021-commuting-cn-conjecture2. Theorem 5.4 of Tak,
Dutta and Nath, arXiv:2605.22160v1, states the strict inequality E_CN(H) < B(n) for unions of
cliques; it fails exactly when H is a single clique or two isolated vertices, so only the
non-strict non-hyperenergetic bound is attributable to it, and Ma and Zhang record Proposition 7
as its correction. The definitions of the common-neighbourhood matrix and energy are those of
Nath, Fasfous, Das and Shang, Symmetry 13 (2021), 1651, recorded in `nath2021commutingcn`.

## Statement

For a finite simple graph H, CN(H) has zero diagonal and off-diagonal entries counting common
neighbours; E_CN(H) is the sum of the absolute values of its real eigenvalues with
multiplicity. Put B(n) = 2(n - 1)(n - 2). If H is the disjoint union of k >= 1 complete graphs
K_(s_i) with s_i >= 1 and n = sum s_i, then E_CN(H) = 2 sum (s_i - 1)(s_i - 2) <= B(n), with
equality exactly when k = 1, or k = 2 and s_1 = s_2 = 1.

## Repository form

The repository states the result for the graph on any finite vertex type whose cliques are the
fibres of an arbitrary labelling map, so the clique orders are the fibre cardinalities and k is
the number of labels attained. The energy is pinned from both sides: writing Pi for the
orthogonal projection onto vectors constant on each clique, the common-neighbour matrix is
W Pi - W'(1 - Pi) with nonnegative clique-constant weights W = (s - 2)(s - 1) and
W' = max(s - 2, 0), and S = 2 Pi - 1 satisfies -1 <= S <= 1 with tr(CN S) equal to the trace of
both parts. The equality analysis uses the identity g(a + N) - g(a) - g(N) = 2aN - 2 for
g(s) = (s - 1)(s - 2). With no labels attained the vertex set is empty, the energy is 0 and the
bound B(0) = 4 is strict, so no hypothesis k >= 1 is needed.

## Neighbourhood-clique bound

Lemma 1 in Section 1 of the same version states, for every finite simple graph H with m edges, r
vertices of positive degree and degrees d(v), that E_CN(H) <= 2 sum_v max(d(v) - 1, 0) = 4m - 2r;
since H is arbitrary, isolated vertices and the empty graph are covered. The weaker bound 4m is
credited there to Jannat, Nath and Das, Remark 4.7, equation (6). The
repository proves it from CN(H) = A^2 - D = sum_v (a_v a_v^T - diag a_v), where a_v is the
indicator of the neighbourhood of v: with the averaging projection Pi_v onto that neighbourhood,
each summand is (d_v - 1) Pi_v - (diag a_v - Pi_v), both parts are positive semidefinite, and the
energy of a difference of positive semidefinite matrices is at most the sum of their traces.

## Finite noncommutative rings

Corollary 3 in Section 2 of the same version states, for every finite noncommutative associative
ring R, not assumed unital and with no commutative-centralizer assumption, with z the order of
the center and n the number of noncentral elements, that n >= z + 2 >= 3 and that the
common-neighbourhood energy of the commuting graph on the individual noncentral elements is at
most n(n - z - 2) < 2(n - 1)(n - 2). Corollary 4 of the same section gives, for finite
nonabelian groups and finite noncommutative rings, E_CN <= 2 sum_(x not central)
max(|C(x)| - z - 2, 0) and, with p the least prime divisor of the order,
E_CN <= 2n((n + z)/p - z - 1). The commutative-centralizer case was posed by Fasfous and Nath
as Conjecture 3.12 and proved by Tak, Dutta and Nath as Corollary 5.5.

The repository states these for every finite ring whose multiplication distributes over
addition, associative or not, with the commutative center {x : xy = yx for all y}; the
associative statements of Corollaries 3 and 4 are the specialisation. The centralizer of a
noncentral element is a proper additive subgroup equal to the disjoint union of the center, the
element and its graph neighbours, so its index is a divisor of |R| exceeding one, and the center
is a proper additive subgroup of it. This gives the chain
2 sum max(|C(x)| - z - 2, 0) <= n max(2(n + z)/p - 2z - 4, 0) <= n max(n - z - 4, 0)
<= n(n - z - 2), together with n >= 3z and z | n.

## Finite nonabelian groups

Theorem 2 of the same version proves, for every finite nonabelian group with z the order of the
center and n the number of noncentral elements, that z >= 1, n >= z + 2 >= 3 and that the
common-neighbourhood energy of the commuting graph on the individual noncentral elements is at
most n(n - z - 2) < 2(n - 1)(n - 2), which strengthens Nath–Fasfous–Das–Shang Conjecture 2.
Corollary 4 gives, for these groups as for rings, E_CN <= 2 sum_(x not central)
max(|C(x)| - z - 2, 0) and E_CN <= 2n((n + z)/p - z - 1) with p the least prime divisor of the
order. The repository proves the centralizer identity deg(x) = |C(x)| - z - 1, the index bound
p |C(x)| <= |G| and 4z <= |G|, and states the chain
2 sum max(|C(x)| - z - 2, 0) <= n max(2(n + z)/p - 2z - 4, 0), which lies below both
2n((n + z)/p - z - 1) and n max(n - z - 4, 0) <= n(n - z - 2), together with n >= 3z and z | n.
