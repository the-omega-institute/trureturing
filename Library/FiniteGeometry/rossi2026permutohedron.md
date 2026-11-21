---
bibkey: rossi2026permutohedron
authors: Giovanni Rossi
year: 2026
title: "Beyond geometric lattices: pseudo-atoms and redundant join representations in the face lattice of the permutohedron"
doi: 10.48550/arXiv.2611.25741
url: https://arxiv.org/abs/2611.25741v1
claim: "What is the smallest dimension of a binary Hamming cube realizing twice the atom metric on all permutations?"
strata_touched:
  - D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension
license: citation-only
triage: anchor
---

# Rossi, the permutohedron and binary Hamming dimension

## Verified locator

DOI: 10.48550/arXiv.2611.25741

URL: https://arxiv.org/abs/2611.25741v1

Giovanni Rossi, *Beyond geometric lattices: pseudo-atoms and redundant join representations in the
face lattice of the permutohedron*, arXiv:2611.25741v1, §10.3 item 8, p. 26, asks:

> Embeddings in the hypercube. The distance δ on atoms is half the Hamming distance between the incidence vectors of the cut sets, so (Sₙ, δ) embeds isometrically, up to the factor 2, in a cube of dimension 2ⁿ − 2. What is the smallest dimension of such an embedding?

The paper uses n ≥ 3 by standing convention. Definition 5.9, p. 11, defines δ as the rank of the
join of two atoms. Its following paragraph identifies δ with the number of proper ranks at which
their unordered prefixes differ. Theorem 5.10(1), pp. 11–12, identifies 2δ with the cardinality of
the symmetric difference of the two cut families and with ordinary Hamming distance on their
incidence words. The cut family determines the permutation by recovering successive entries of its
prefix chain. [Question](https://arxiv.org/pdf/2611.25741v1#page=26) · [Definition and scale](https://arxiv.org/pdf/2611.25741v1#page=11)

The formal theorem `D5/S3/Combinatorics/Graph/PrefixHamming/ExactDimension.minimum_hamming_dimension`
uses twice the proper-rank mismatch count. It gives minimum dimension 12 at n = 4 and
2ⁿ − 2 otherwise, for every n ≥ 3.

## Related results

- Ovchinnikov's *Graphs and Cubes* is the source for the inversion-set graph embedding discussed in
  Rossi's Remark 5.16. The conventional permutohedron graph distance concerns adjacent-swap
  path length. For example, 123 and 321 have graph distance three and two unequal proper
  prefixes. Graham–Winkler and Wilkeit also study graph-distance embeddings.
  [Ovchinnikov](https://doi.org/10.1007/978-1-4614-0797-3) · [Graham–Winkler](https://doi.org/10.1090/S0002-9947-1985-0776391-5) · [Wilkeit](https://doi.org/10.1016/0095-8956(90)90073-9)
- Bandelt and Dress study canonical split decompositions of finite metrics. A split decomposition
  alone leaves the minimum number of unit binary coordinates at the specified scale to be
  determined. [Bandelt–Dress](https://doi.org/10.1016/0001-8708(92)90061-O)
- Minder, Sauerwald and Wegner study equilateral binary codes, building on classical work including
  Deza. The distance-two star-or-triangle classification accounts for the possible savings at one
  rank. The additional requirement here is to control shared coordinates between distinct ranks.
  Attaching an extra root leaf to turn each permutation into a rooted caterpillar gives an
  equivalent split symmetric-difference metric in Robinson–Foulds terminology.
  [Minder–Sauerwald–Wegner, §2–3](https://arxiv.org/abs/1408.5027v1) · [Deza](https://doi.org/10.1016/0012-365X(73)90065-4) · [Robinson–Foulds](https://doi.org/10.1016/0025-5564(81)90043-2)

## Bounded prior-resolution evidence

The exact-title, prefix-set metric, hypercube and anchored Robinson–Foulds searches recorded
with issue #32776 found no equivalent minimum-dimension settlement in their searched scope.
The independent reading covered named graph-isometry, split-decomposition and equilateral-code
sources. Several citation indexes and the Graham–Winkler and Bandelt–Dress publisher full texts
had access limits. Priority outside the searched scope remains unverified.
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/32776)
