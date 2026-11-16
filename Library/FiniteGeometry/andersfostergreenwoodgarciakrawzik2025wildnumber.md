---
bibkey: andersfostergreenwoodgarciakrawzik2025wildnumber
authors: Katie Anders; Briana Foster-Greenwood; Rebecca Garcia; Naomi Krawzik
year: 2025
title: The Wild Number of an Edge-Colored Graph
doi: 10.48550/arXiv.2508.06711
url: https://arxiv.org/abs/2508.06711v1
claim: 'Question 7.5 asks how far Algorithm 5.10 can be from the actual wild number, including whether its additive error can exceed one or two.'
strata_touched:
  - D5/S3/Combinatorics/EdgeLabeling/WildNumber/Greedy
  - D5/S3/Combinatorics/EdgeLabeling/WildNumber/WheelCertificate
  - D5/S3/Combinatorics/EdgeLabeling/WildNumber/Result
license: citation-only
triage: anchor
---

# The Wild Number of an Edge-Colored Graph

## Verified locator

DOI: 10.48550/arXiv.2508.06711

Source: https://arxiv.org/abs/2508.06711v1

Version 1. Section 7, PDF page 21, Question 7.5:

> How far off can Algorithm 5.10 be from the actual wild number? Is it ever off by more than one? or two?. . .

## Mathematical definitions

PDF page 1:

> For any color cᵢ ∈ C, let Eᵢ(G) = {e ∈ E(G) : γ(e) = cᵢ}, and let Gᵢ be the graph with vertex set V(G) and edge set Eᵢ(G).

PDF page 2:

> For any color cᵢ, define the graph Gᵢᵂ to be the subgraph of G with vertex set V(G) and edge set W ∪ Eᵢ(G).

PDF page 2:

> If the set of edges W is such that for every cᵢ ∈ C, the subgraph Gᵢᵂ is connected, then W is a color-connecting set.

PDF page 2:

> A color-connecting set of minimal size is an ideal wild set. The wild number of G, denoted wld(G), is the size of an ideal wild set of G.

PDF page 2:

> The dip number of an edge e is δ(e) = #{i : edge e helps color cᵢ} = ∑ᵢ (κ(Gᵢ) − κ(Gᵢᵉ)), which tells us how many colors we can help by coloring that edge wild.

PDF page 15:

> The potential of an edge e in an edge-colored graph G is the nonincreasing dip sequence of the graph G/e.

PDF page 15:

> Order the edges in G/W with the highest dip number lexicographically by potential in G/W (i.e., compare first terms of potential, highest wins; if tie, compare next term; etc.).

PDF page 15:

> Initialize by letting W = ∅. While the graph G/W is not color-connected, do the following two steps:

PDF page 15:

> When G/W is color-connected, return the set W.

The edge coloring is surjective. Natural subtraction in dip is truncated at zero. Example 5.9 includes the contracted edge with dip zero in the potential sequence. A run starts at the empty set and performs exactly the successive edge insertions, retaining every tie choice.

## Settlement and boundary

The rooted amalgamation of r copies of the Example 5.12 wheel, for r ≥ 1, has wild number 5r, and every greedy output has cardinality 6r. A greedy output exists. The construction therefore has additive error r and ratio 6/5. It does not establish unbounded multiplicative error.

The finite wheel has eight vertices and fourteen edges. Its four edge classes, in the order of the source's Example 5.12, are:

- {01, 03, 04};
- {02, 06, 45, 67};
- {05, 07, 12, 17, 56};
- {23, 34}.

The set {03, 07, 12, 45, 56} connects every color class. Identifying the roots of the blocks preserves each block's dip numbers. Common multiset addition preserves the relevant lexicographic comparisons, which permits every global greedy run to be restricted to its blocks.

## Computational evidence

The experiment is in the private repository `the-omega-institute/trureturing-experiments`, commit `fee5fd5f673a7ff07d7a2b8f5df4792810d3cbe8`, at `docs/reports/anders-foster-greenwood-garcia-krawzik-2025-wild-number-greedy-gap/check.py`, SHA-256 `583b5ca75466f182823c210ee7b27c2cd8fd4de94c8083801a7d2c948c8a1952`. Its recorded exit code is 0.

The star-amalgamation experiment is at commit `34215f188cb483c0d1791c8b4e5807817858331f`, the same directory's `star.py`, SHA-256 `8ed18e5fb05414ff2a0a9f968a8c2195bc2a416939981b3edff0e36ad5df57a7`. The recorded command `/opt/homebrew/bin/python3 star.py` exits 0 and gives greedy cardinalities {6}, {12}, {18} for r = 1, 2, 3. These finite readings corroborate the construction; the quantified mathematical conclusion is carried by Lean.

## Literature boundary

The bounded source and ownership screen is recorded in issue #20098. Completeness of the literature search is ASSUMED-UNVERIFIED. No absence or originality claim follows from a bounded search.
