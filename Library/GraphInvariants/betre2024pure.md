---
bibkey: betre2024pure
authors: Kassahun H Betre; Yan X Zhang; Carter Edmond
year: 2024
title: "Pure Simplicial and Clique Complexes with a Fixed Number of Facets"
doi: 10.48550/arXiv.2411.12945
url: https://arxiv.org/html/2411.12945v1
claim: "Theorem 3.1 characterizes finite clique complexes by requiring the union of the three pairwise intersections of any three facets to be a face."
strata_touched:
  - D5/S3/Combinatorics/Graph/HereditaryFlip/Majority
license: citation-only
triage: anchor
---

# Majority and clique complexes

Theorem 3.1 of arXiv:2411.12945v1 states that a simplicial complex with
facets F1,...,Fn is a clique complex if and only if
(Fi intersection Fj) union (Fi intersection Fk) union (Fj intersection Fk)
is a face for each three-element subset of facet indices. The complex
contains the empty face. Heredity transfers the condition from facets to
arbitrary faces; repeated inputs have a majority contained in an input.
Clique complexes are determined by their singleton and pair faces.

Yan-Ting Xie and Shou-Jun Xu, "Characterizing simplex graphs" (2025),
arXiv:2503.17160v1, Theorem 1.5, also identify finite clique or independence
complexes by the Median Property. Its surrounding discussion explicitly
relates that property to the earlier facet criterion.

The formal finite-support statement uses an arbitrary ambient type with
decidable equality. It includes empty and singleton constraints, so it
also allows absent vertices and the empty family. The universal least
majority-closed extension follows by induction on support cardinality and
does not assume heredity of competing extensions. These are classical
combinatorial statements and their consequences; no novelty is claimed.
The module contains no graph metric or metric median theorem.
