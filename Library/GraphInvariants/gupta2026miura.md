---
bibkey: gupta2026miura
authors: Chakshu Gupta
year: 2026
title: "Height functions on the m × n Miura-ori flip graph: degree sequence and diameter"
doi: 10.48550/arXiv.2606.22614
url: https://arxiv.org/abs/2606.22614v2
claim: "Inequality (4), p. 14: max_ϕ disp(ϕ) ≤ D(m, n) for integer 1-Lipschitz functions on the rectangular grid."
strata_touched:
  - D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion
license: citation-only
triage: anchor
---

# Gupta, *Height functions on the m × n Miura-ori flip graph*

## Verified locator

DOI: 10.48550/arXiv.2606.22614

Source: https://arxiv.org/abs/2606.22614v2

## Source statements

Section 2, p. 2:

> Every construction in this paper lives on the grid graph Gm,n, with vertex set {(i, j) : 1 ≤ i ≤ m, 1 ≤ j ≤ n} and each vertex joined to its horizontal and vertical neighbours;

Section 4, p. 13:

> Writing disp(ϕ) = min_{K∈Z} Σ_v |ϕ(v) − K| for the ℓ1 median-dispersion of an integer function ϕ on the grid

Theorem 4.1, p. 13:

> Let D(m, n) = min_{K∈Z} Σ_{i=1}^m Σ_{j=1}^n |(i + j) − K|. Then diam OFG(M_{m,n}) ≥ D(m, n) for all m, n ≥ 1.

Inequality (4), p. 14:

> By Proposition 4.2 and Theorem 4.1, the diameter equals D(m, n) as soon as no integer 1-Lipschitz function on G_{m,n}, realisable or not, has dispersion exceeding D(m, n): max_ϕ disp(ϕ) ≤ D(m, n). (4)

The integer sums use each vertex once. Lean represents source cell (i,j) by (i−1,j−1) in Fin m × Fin n. The natural-valued minimum is the infimum of the nonempty range of integer-center costs. The source's coordinate sum remains one-indexed in D.

## Scope

The repository proves the universally quantified inequality for all natural dimensions, including empty rectangles. The proof sorts rows and columns, compares centered absolute deviations using FKG, and rounds a rational center to an integer without increasing cost. The origami diameter consequence also uses the source's Theorem 4.1 and Proposition 4.2, which are not formalized in this module. Conjecture 4.6 for abstract ν-chains remains open.

The literature screen in issue #19839 found no earlier settlement within its searched scope. Completeness is ASSUMED-UNVERIFIED.
