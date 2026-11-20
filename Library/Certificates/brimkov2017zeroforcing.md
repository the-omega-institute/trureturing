---
bibkey: brimkov2017zeroforcing
authors: Boris Brimkov
year: 2017
title: "Graph Coloring, Zero Forcing, and Related Problems"
doi: null
url: "https://repository.rice.edu/server/api/core/bitstreams/c29c77d5-534a-4c5d-bd83-09121784af53/content"
claim: "Proposition 7.7: if n >= 2, the connected forcing polynomial of the path is Z_c(P_n; x) = 2x + sum_(i=2)^n (n - i + 1) x^i. Proposition 7.8: if n >= 3, Z_c(C_n; x) = n sum_(i=2)^(n-1) x^i + x^n. Proposition 7.11: the connected forcing polynomial of k pendant paths of b_1, ..., b_k vertices attached to a vertex; with unit arms it gives Z_c(K_(1,n-1); x) = (n - 1) x^(n-1) + x^n for n >= 4."
strata_touched:
  - D5/S3/Combinatorics/Graph/ZeroForcing/PathConnectedForcing
  - D5/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing
  - D5/S3/Combinatorics/Graph/ZeroForcing/CycleConnectedForcing
license: citation-only
triage: anchor
---

# Connected forcing polynomials of the path, the cycle and the star

## Verified locator

PhD thesis, Rice University, May 2017, Chapter 7, Proposition 7.7, printed pages 165–166,
Proposition 7.8, printed page 166, and Proposition 7.11, printed pages 168–169. Source
PDF: https://repository.rice.edu/server/api/core/bitstreams/c29c77d5-534a-4c5d-bd83-09121784af53/content .

## Source statement

> Definition 7.1. Let G be a graph. Let z(G; i) and z_c(G; i) respectively be the number of zero
> forcing sets and the number of connected forcing sets of G with cardinality i. The zero forcing
> polynomial of G is defined as Z(G; x) = Σ_{i=Z(G)}^n z(G; i) x^i. The connected forcing
> polynomial of G is defined as Z_c(G; x) = Σ_{i=Z_c(G)}^n z_c(G; i) x^i.

> Proposition 7.7. If n ≥ 2, Z_c(P_n; x) = 2x + Σ_{i=2}^n (n − i + 1) x^i.

> Proposition 7.8. If n ≥ 3, Z_c(C_n; x) = x^n + Σ_{i=2}^{n−1} n x^i.

The source's proof: Z_c(C_n) = 2; a connected forcing set of size 2 ≤ i ≤ n − 1 is determined by
its first vertex in the cyclic order, giving n of them, and the whole cycle is the only set of
size n.

> Proposition 7.11. Let G be a graph composed of k pendant paths attached to a vertex v, where
> the ith pendant path has b_i vertices, 1 ≤ i ≤ k. Then,
> Z_c(G; x) = Σ_{j=1}^n ( s(j − 1; b_1, …, b_k) + Σ_{ℓ=1}^k s(j − 1; b_1, …, b_{ℓ−1}, b_{ℓ+1}, …, b_k) ) x^j.

Here s(a; b_1, …, b_k) is, by the source's Definition 7.2, the number of k-tuples of positive
integers with sum a whose ith entry is at most b_i; it is 0 when a < k or a > Σ b_i, and
s(0; ) = 1 for the empty tuple. The source's proof: every connected
set containing v and all but one neighbour of v is a connected forcing set, and the connected
forcing sets of size j split by which neighbour of v, if any, is missing.

The proof of Proposition 7.7: either end vertex is a connected forcing set of size 1; for 2 ≤ i ≤ n a
connected forcing set of size i is determined by its vertex of smallest label in a depth-first
order from an end, which leaves n − i + 1 choices.

## Mathematical scope

PathConnectedForcing.result states the coefficients of Z_c(P_n; x) for Mathlib's pathGraph n and
the connected forcing sets of ConnectedForcingCrossingRefutation (zero forcing sets inducing a
connected subgraph): z_c(P_n; 0) = 0, z_c(P_n; 1) = 2, and z_c(P_n; i) = n + 1 − i for every
i ≥ 2, which is 0 for i > n. PathConnectedForcing.connected_forcing_iff characterizes the
connected forcing sets of P_n, n ≥ 2: the intervals with at least two vertices and the two end
vertices. The source's Theorem 7.2(6) states that either end of P_n, n ≥ 2, is a zero forcing set;
that an interior vertex alone forces nothing is used in its count without a separate statement and
is proved here. The coefficient z_c(P_n; 0) = 0 holds for every n.

StarConnectedForcing.result states the coefficients of Z_c for the star K_(1,n-1) (starGraph n
on Fin n with centre 0), n ≥ 1: z_c(i) = [i = n] + (n − 1)[i = n − 1] + (n − 1)[i = 1, n ≤ 3].
For n ≥ 4 this is Proposition 7.11 with k = n − 1 unit arms: s(j − 1; 1, …, 1) is 1 at j = n and
each omitted arm contributes 1 at j = n − 1. For n = 1 the formula with k = 0 gives x, which is
correct. For n = 2 and n = 3 the formula with unit arms gives x + x^2 and 2x^2 + x^3, omitting
the n − 1 single leaves, which force a star with at most two leaves. For every n ≤ 3 result
states that the coefficients agree with those of the path.
StarConnectedForcing.connected_forcing_iff characterizes the connected forcing sets of the star.

CycleConnectedForcing.result states the coefficients of Z_c(C_n; x) for Mathlib's cycleGraph n
and every n: z_c(C_n; i) = 1 for i = n ≠ 0, n for 1 ≤ i < n when i ≥ 2 or n = 2, and 0
otherwise. For n ≥ 3 this is the source's formula, which it states as a second clause. The
source's form also holds for n = 1, while for n = 0 no set is connected and for n = 2 each single
vertex is a connected forcing set, giving Z_c(C_2; x) = 2x + x^2.
CycleConnectedForcing.connected_forcing_iff characterizes the connected forcing sets of C_n as
the arcs of at least two vertices, together with the single vertices when n = 2.
