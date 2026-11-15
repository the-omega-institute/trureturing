---
bibkey: onn2023supmodular
authors: Shmuel Onn
year: 2023
title: On Supmodular Matrices
doi: 10.48550/arXiv.2309.07700
url: https://arxiv.org/abs/2309.07700v1
claim: "The unnumbered referee question before Lemma 2.2 asks for the count and characterization of permutations good at every adjacent square in every dimension."
strata_touched:
  - D5/S3/Combinatorics/Permutation/OnnGoodPermutationStructure
  - D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2309.07700
Source: https://arxiv.org/abs/2309.07700v1

Section 2, page 4, immediately before Lemma 2.2.

The Introduction fixes the rank-array interpretation:

> For an $m\times n$ matrix $\sigma$ whose entries form a permutation of $1,2,\dots,mn$, let $A^{\sigma}$ be obtained from $A$ by permuting its entries such that $\sigma_{i,j}<\sigma_{r,s}$ implies $A^{\sigma}_{i,j}\leq A^{\sigma}_{r,s}$.

Section 2 defines:

> We say an $m\times n$ matrix $\sigma$ whose entries are a permutation of $1,2,\dots,mn$ is *good on $i,j$* with $1\leq i<m$ and $1\leq j<n$ if the maximum among $\sigma_{i,j},\sigma_{i,j+1},\sigma_{i+1,j},\sigma_{i+1,j+1}$ is either $\sigma_{i,j}$ or $\sigma_{i+1,j+1}$ and the minimum among these entries is either $\sigma_{i,j+1}$ or $\sigma_{i+1,j}$.

The following unnumbered question reads:

> An interesting question suggested by a referee is to count and characterize, for every $m$ and $n$, those permutations which are good for all $1\leq i<m$ and $1\leq j<n$.

Theorem 1.3 already gives the nonempty dimensions:

> For $m\leq n$, a universal $\sigma$ exists if and only if $m=1,2$ or $m=n=3$.

The formal arrays are equivalences `(Fin m × Fin n) ≃ Fin (m*n)`.
Their ranks become the source's labels by adding one; coordinates are zero-based.
Goodness uses exactly the displayed maximum and minimum positions. In a two-row
array a unique sign transition gives two disjoint increasing chains. The complete
answer counts these by even-cardinality subsets; the two three-by-three types
have center label 5 and contribute 36 arrays each. These count and chain results
are repository-derived. The zero range is source-known.

The source's other questions about covering numbers, non-permutable real matrices
and decision complexity remain open here. Counts allowing tied labels are also
outside this result.

The final journal version is *Linear and Multilinear Algebra* 72(14), 2341–2346,
DOI `10.1080/03081087.2023.2256939`. Its full mathematical text was inaccessible
in the literature screen recorded in issue #26707. The arXiv manuscript and the
author-posted manuscript retain the question. Priority and completeness of the
literature screen are `ASSUMED-UNVERIFIED`.

Finite corroboration is in `the-omega-institute/trureturing-experiments`, commit
`0ef78b1c4735982a86a1626e00b2f727bbbd9295`,
`docs/reports/onn-2023-good-permutation-enumeration/check.py`, SHA256
`bfc565ffaac0ef0e7b24b2885ca285692ffa2648b679ca01840aa0e373bc0e82`.
Issue #26707 reports exit 0 with `ALL_CHECKS_OK` for 35 positive ordered dimension
pairs with product at most 12, chain-set equality through width 6 in both
orientations, and an independent enumeration of all 9! three-by-three arrays.
These computations provide no premise of the general proof.
