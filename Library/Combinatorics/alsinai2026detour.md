---
bibkey: alsinai2026detour
authors: Ammar Alsinai and Hanan Ahmed
year: 2026
title: Detour different-distance sets in graphs
doi: 10.48550/arXiv.2611.26653
url: https://arxiv.org/abs/2611.26653v1
claim: "Problem 4.3 asks for both detour different-distance numbers of sunlets. Theorem 2.14(i) gives the triangle sunlet, the proof of Theorem 2.1 and Lemma 3.3 give the distance calculation, and Lemma 3.4 gives the core–leaf DDD pairs."
strata_touched:
  - D5/S3/Combinatorics/Graph/Sunlet/DetourPath
license: citation-only
triage: anchor
---

# Alsinai and Ahmed, Detour different-distance sets in graphs

Section 1 defines detour distance as the edge length of a longest simple path
and sets the diagonal to zero. Definition 1.1 takes the minimum and maximum
cardinalities of inclusion-maximal nonempty proper sets whose vertices have
distinct detour distances from every outside vertex.

Section 2.8 defines the corona. Theorem 2.14(i) applies to the triangle sunlet
because both the triangle and the two-vertex complete graph meet its
Hamiltonian-connectedness hypotheses. The proof of Theorem 2.1 gives the
longer-arc formula for distinct cycle vertices. The block sum of Lemma 3.3
adds one edge for each leaf endpoint at distinct indices and gives distance
one across the single-edge block of a core–leaf pair. Lemma 3.4 establishes
that each such pair is a DDD set.

Problem 4.3 (page 13) asks:

> Determine ddD for lollipops, barbells and tadpoles, and both numbers for grids, sunlets, snakes and generalized Petersen graphs.

For the sunlet clause with at least four cycle vertices, the repository proof
shows that every DDD set has at most two vertices and every singleton extends
to a core–leaf DDD pair. Both extrema of the maximal-set orders are therefore two.

## Verified locator

- DOI 10.48550/arXiv.2611.26653
- Versioned record https://arxiv.org/abs/2611.26653v1
- Section 1 and Definition 1.1, proof of Theorem 2.1, Section 2.8 and Theorem 2.14(i), Lemmas 3.3–3.4, and Section 4 Problem 4.3, page 13. https://arxiv.org/pdf/2611.26653v1
