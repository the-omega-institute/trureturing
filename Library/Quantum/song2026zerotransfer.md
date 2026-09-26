---
bibkey: song2026zerotransfer
authors: Xingkun Song, Huiqiu Lin
year: 2026
title: "Zero transfer on mixed graphs"
doi: 10.48550/arXiv.2608.10643
url: https://arxiv.org/abs/2608.10643v1
claim: "The paper characterizes zero transfer of the continuous-time quantum walk on mixed graphs through the Hermitian adjacency matrix, proves that connected oriented circulant graphs of prime order have no zero transfer, and conjectures from computations up to order 20 that for order n ≡ 2 (mod 4) zero transfer between a vertex v and 0 forces v to be odd."
strata_touched:
  - D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer
license: citation-only
triage: anchor
---

# Zero transfer on mixed graphs

Song and Lin use the Hermitian adjacency matrix of a mixed graph, with entry
`i` on an arc `u → v`, `-i` on the reversed arc, `1` on an undirected edge and
`0` otherwise, and the transition matrix `U(t) = exp(-i t H)`. A graph has zero
transfer from `u` to `v` if `U(t)_{u,v} = 0` for every `t ≥ 0`; by unitarity
this is symmetric, and the paper speaks of zero transfer between `u` and `v`.
It shows that zero transfer between distinct vertices is equivalent to the
vanishing of `(H^k)_{u,v}` for every `k ≥ 1`.

Section 3 treats the oriented circulant graphs `G(ℤ_n, C)`, with arcs
`a → b` for `b - a ∈ C`, `C ⊆ ℤ_n ∖ {0}` and `C ∩ -C = ∅`, all assumed
connected. It proves that there is no zero transfer when `n` is prime, gives
the order-21 example `C = {2, 10, 12, 15, 16, 17}` with zero transfer at
distances 7 and 14, and, after an exhaustive search for `n ≤ 20`, states
Conjecture 3.1:

> Let Γ = G(ℤ_n, C) be an oriented circulant graph with n ≡ 2 (mod 4). If
> zero transfer occurs between vertex v and 0, then v must be odd.

The remark after it records that a general algebraic proof remains open.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2608.10643
- URL: https://arxiv.org/abs/2608.10643v1
- Version and location: arXiv:2608.10643v1 (2026-08-11, the only version), source file `zero_state_2026_5.21N.tex`: §1 for the Hermitian adjacency matrix, the transition matrix and the definition of zero transfer; §3 for oriented circulant graphs, the standing connectedness assumption and Conjecture 3.1 (the first `con` environment of §3, numbered within sections).
