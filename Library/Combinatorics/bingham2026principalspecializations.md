---
bibkey: bingham2026principalspecializations
authors: Aram Bingham, Kyle Celano, Patricia Commins, Rosa Orellana, Jianping Pan, and Mary Claire Simone
year: 2026
title: Principal specializations of the t-chromatic symmetric function
doi: 10.48550/arXiv.2610.31785
url: https://arxiv.org/abs/2610.31785v1
claim: "Remark 3.11 asks whether every positive-j listed pair has unequal second and equal third ordinary principal specializations, and whether the base and these pairs exhaust the phenomenon."
strata_touched:
  - D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family
  - D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarUniquenessRefutation
license: citation-only
triage: anchor
---

# Bingham et al., *Principal specializations of the t-chromatic symmetric function*

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2610.31785

Source: https://arxiv.org/abs/2610.31785v1

Version 1, submitted 22 October 2026. Definition 2.1 defines the caterpillar. Definition 2.4 allows every proper coloring into the available color set, without requiring every color to occur. Definition 2.7 defines the ordinary chromatic symmetric function. Definition 2.9 and equation (2.1) identify its finite principal specialization with the proper-coloring weight sum. Remark 3.11 asks both the family question and the exhaustive-pairs question.

## Source statement

Remark 3.11:

> Additionally, we verified that for j ≤ 7, each pair (5,j,j,4,3) and (4,j,j,5,3) exhibits this phenomenon, raising the following questions. Do (5,j,j,4,3) and (4,j,j,5,3) exhibit this phenomenon for all j? And if so, do they continue to be the only pairs of compositions which do?

Here “this phenomenon” means that the ordinary third principal specializations agree as polynomials and the ordinary second principal specializations differ. The source represents compositions by positive parts and changes colors to 0 through k−1 in equation (2.1).

## Scope

The first formal target is the family question for every positive integer j. The distinct second target is the unrestricted exhaustive-pairs assertion, including the base pair and the whole positive-j family up to unordered graph isomorphism. BinghamCaterpillarUniquenessRefutation uses the eighteen-vertex compositions (2,2,2,2,2,1,4,3) and (2,2,3,2,3,4,2) to refute it. Their second polynomials are X^8+X^10 and 2X^9; their third polynomials agree. Eight vertices with two distinct neighbors in the first graph exclude isomorphism to any listed member, whose spine length is three or five. Both results use actual graph-coloring sums. The second module proves the injective coefficient-extension bridge from Z[X] to the source's C[X]. Neither target concerns surjective colorings, a t refinement, numerical values of X, or the four-color conjectures. A classification of every other pair and counterexample minimality remain unresolved.

The source is literature-attested. The family proof is a repository derivation. The preregistration's bounded literature screen located no earlier settlement; citation and third-party code searches were incomplete, so no exhaustive absence or originality claim follows.
