---
bibkey: adamsonflahertypotapovspirakis2024twoswap
authors: Duncan Adamson; Nathan Flaherty; Igor Potapov; Paul G. Spirakis
year: 2024
title: Structural and Combinatorial Properties of 2-swap Word Permutation Graphs
doi: 10.1007/978-3-031-55601-2_5
url: https://arxiv.org/abs/2307.01648v3
claim: The closing conjecture asserts that the greedy algorithm of Lemma 4 can find a shortest path between every pair of vertices of a 2-swap word graph.
strata_touched:
  - D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1007/978-3-031-55601-2_5

Source: https://arxiv.org/abs/2307.01648v3

Version 3, 27 June 2024. Definition 1 and the Parikh vector are on page 4;
the configuration graph is on page 5; Lemma 4 and Algorithm 1 are on page 9;
the conjecture is in Section 5, page 23.

## Statement

Section 5, page 23:

> For the 2-swap graph specifically, we leave open the problem of determining the shortest path between two given words w and v. We conjecture that the simple greedy algorithm used to derive the upper bound in Lemma 4 can be used to find the shortest path between any pair of vertices.

Definition 1, page 4:

> Given a word w∈Σⁿ and pair i,j∈[n], i<j such that w[i]≠w[j], the 2-swap of w by (i,j), denoted w∘(i,j), returns the word w[1,i−1]w[j]w[i+1,j−1]w[i]w[j+1,n].

Page 4:

> Given a word w∈Σⁿ, the Parikh vector of w, denoted P(w) is the σ-length vector such that the ith entry of P(w) contains the number of occurrences of symbol i in w, formally, for i∈[σ], P(w)[i]=|{j∈[n] | w[j]=i}|, where n=|w|.

Page 5:

> For a given alphabet Σ and Parikh vector P, the configuration graph of Σ∗|P is the undirected graph G(P)={V(P),E(P)} where:

> Informally, the configuration graph for a given Parikh vector P is the graph with each vertex corresponding to some word in Σ∗|P, and each edge connecting every pair of words w,u∈Σ∗|P such that there exists some 2-swap transforming w into u.

Proof of Lemma 4, page 9:

> We assume, without loss of generality, that P[1]≥P[2]≥⋯≥P[σ].

Algorithm 1, page 9:

> for x ∈ Σ \ {1} do
>
> i ← index of kᵗʰ occurrence of x in w
>
> j ← index of kᵗʰ occurrence of x in v
>
> Apply all 2-swaps in S to w and set S ← ∅

## Mathematical scope

The formal proposition allows every reference letter of maximal count and every
non-increasing ordering of the other letters. It requires only that the number
of generated pairs with distinct indices equal the graph distance, without
requiring these pairs to form a legal path reaching the target. This weaker
necessary condition already fails for the binary family
w=0ᵏ1ᵏ and v=1·0ᵏ⁻¹·1ᵏ⁻¹·0, for every k≥2: the distance is one and either
allowed order generates k nontrivial pairs.

The experiment is in `the-omega-institute/trureturing-experiments`, commit
`995dd5c17c9dc8f5dfdcfe1fc921644e36f489a1`, at
`docs/reports/adamson-flaherty-potapov-spirakis-2023-two-swap-greedy/check.py`,
SHA-256 `64fcb9c8957d1d5274a546bc69eff1d61da07791187867257cf3c4710536d34e`.
It exits 0 with `RESULT PASS`. The unbounded conclusion is proved by Lean;
the experiment checks only its stated finite ranges.

The literature screen in issue #19317 includes the paper and Flaherty's later
thesis. Completeness of that screen is ASSUMED-UNVERIFIED. The shortest-path
problem for unbounded alphabets and its complexity remain open here.
