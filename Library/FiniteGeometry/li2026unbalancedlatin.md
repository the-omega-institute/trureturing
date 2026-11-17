---
bibkey: li2026unbalancedlatin
authors: Zhengyu Li, Vijay Ganesh
year: 2026
title: "How Unbalanced Must a Latin Rectangle Be?"
doi: 10.48550/arXiv.2611.06003
url: https://arxiv.org/abs/2611.06003v1
claim: "Section 10 open problem (5) asks for a direct proof that a perfectly balanced k by n Latin rectangle needs k at least n/2, using bijective coordinate projections."
strata_touched:
  - D5/S3/Combinatorics/Latin/PerfectBalanceDimension
license: citation-only
triage: anchor
---

# Li and Ganesh: balance of Latin rectangles

## Verified locator

DOI: 10.48550/arXiv.2611.06003

URL: https://arxiv.org/abs/2611.06003v1

Version: arXiv:2611.06003v1. Section 2 gives the Latin-rectangle and imbalance definitions. Section 10, open problem (5), printed page 17, asks:

> Show directly that a perfectly balanced k × n rectangle needs k ≥ n/2, using that its coordinate projections are bijections.

The positive-size convention is inherited from the cited Latin-rectangle definitions: 1 ≤ k ≤ n. Each row and column has no repeated symbol. The coordinate of a symbol is its column in a given row, and each coordinate map is a bijection. The pair distance is the sum of absolute column differences. Imbalance sums the absolute deviations from k(n+1)/3 over unordered symbol pairs.

## Scope

The target is this direct dimension bound, including n = 1. It is neither the general ℓ1 Kusner conjecture nor the assertion that every perfectly balanced rectangle is square. The source's question is literature-attested; a new proof in the corresponding Lean module is repository-derived. The bounded readings of Díaz et al. (2017), Ramaswamy–Szeider (2023), and van Dam–Rennen–Husslage (2009) supplied no adopted general theorem giving this bound; this is no worldwide novelty claim.

## Source identity

The qualified PDF SHA-256 is 96ee8560ec19b42fcb7e85e5837dbbecb0504fb90fea76bdb58d1875b6f86c3e. The extracted main TeX SHA-256 is ef12a7890acd2a003e441d01729b36ba3619cec3a847a2498add6a233ef815a4. These identify the documentary sources used for the definitions and question.
