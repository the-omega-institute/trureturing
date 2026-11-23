---
bibkey: gonzalezdeleonwachs2026weighted
authors: Rafael S. Gonzalez D'Leon; Michelle L. Wachs
year: 2026
title: "Weighted bond posets and a new chromatic symmetric function"
doi: 10.48550/arXiv.2608.08692
url: https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13
claim: "Conjecture 4.13(2): for a graph G on n vertices with k connected components and a spanning subgraph H with the same k components, (-1)^(n-k)(mu_G-mu_H) is real-rooted."
strata_touched:
  - D5/S0/Certificates/GonzalezDLeonWachsWeightedBondSource
  - D5/S0/Certificates/GonzalezDLeonWachsThreeVertexMobius
  - D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation
  - D5/S3/Combinatorics/WeightedBond/FiniteOrder
  - D5/S3/Combinatorics/WeightedBond/CountableColors
  - D5/S3/Combinatorics/WeightedBond/PartitionExpansion
  - D5/S3/Combinatorics/WeightedBond/ExponentialSeries
  - D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization
license: citation-only
triage: anchor
---

# Weighted bond posets and a new chromatic symmetric function

Section 2 defines weighted connected-block partitions, their refinement order,
the singleton bottom, and the weighted bond-poset Mobius polynomial. Propositions
2.1 and 2.2 supply the structural background, including the component product.
Theorem 3.1 and formula (3.4) relate these polynomials to the paper's later
constructions.

Conjecture 4.13(2) is stated for an arbitrary graph `G` on `n` vertices with
`k` connected components and a spanning subgraph `H` having the same
`k`; it asserts real-rootedness of `(-1)^(n-k)(mu_G-mu_H)`. It does not impose
connectedness. The formal result targets only part (2) as written.

## Verified locator

- DOI: 10.48550/arXiv.2608.08692
- URL: https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13
- Locator: arXiv:2608.08692v1, Section 2, Theorem 3.1, formula (3.4), and
  Conjecture 4.13(2).
- Retrieved source hash: SHA-256
  `1781237e65346eab7d5119fcf67abb2d795c505d7e99a26e572df891a760773e`.

The bounded literature checks recorded for issue 8501 found no full resolution.
arXiv:2609.15784v1 develops nestohedron recurrences but did not provide a
located resolution of Conjecture 4.13(2); its Mobius-polynomial follow-up was
described as in preparation. This is bounded status evidence, not a worldwide
priority claim.


## Complete-graph specialization

Version 2, Section 5.1 defines the connected-block refinement with color
weights. Equation (7.1) sums the bottom incidence Möbius value of each
element of the countable-color poset against its color monomial. Question
7.1 asks for the specialization to the complete graph with the first
\(r>2\) variables equal to \(t\) and the remaining variables zero. A
partition with \(k\) blocks contributes degree \(n-k\) to this literal
specialization. The forms printed in (7.3) and (7.4) use the reversed
degree \(k-1\).

- Source locator [arXiv:2608.08692v2, Question 7.1](https://arxiv.org/html/2608.08692v2#S7.Thmtheorem1)
- Retrieved HTML SHA-256
  `5fc152746b92a4f77d06f2bd70111f2ff53c9d1ba6df3b4a7c5e09810af4661c`
- Earlier one-block inverse and Lie-symmetric-function coefficients [arXiv:1408.5415](https://arxiv.org/abs/1408.5415)
- Earlier two-color evaluation [arXiv:1309.5527](https://arxiv.org/abs/1309.5527)
