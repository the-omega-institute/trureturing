---
slug: bresar-ferme-hu-packing-domatic-paths
bibkey: bresar2026packingdomatic
doi: 10.48550/arXiv.2610.03477
url: https://arxiv.org/abs/2610.03477v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PackingDomatic/PackingDomaticPath.result
---

# Packing k-Domatic Colourings of Paths Need More Than k + 1 Colours

## Problem

Boštjan Brešar, Jasmina Ferme and Wenjie Hu, *Partitioning an S-packing coloring into broadcast dominating sets*,
arXiv:2610.03477v1, Section 5: "Problem 2. Is it true that χ_{ρ,k}(P_n) ≤ k + 1 for any k ≥ 3 and any n ≥ 2k?"
A packing k-domatic colouring f with colours in [t] keeps two vertices of colour j at distance greater than j and
admits a partition of the vertices into k classes, each broadcast-dominating every vertex x through some a in the
class with d(x, a) ≤ f(a); χ_{ρ,k}(G) is the least such t.

## Motivation

The theorem `D5/S3/Combinatorics/PackingDomatic/PackingDomaticPath.result` answers Problem 2 negatively. Its
counting lemma proves that a packing k-domatic colouring of P_n with colours at most t and n ≥ t + 1 satisfies
15t ≥ 16k − 12; hence χ_{ρ,k}(P_n) ≥ ⌈(16k − 12)/15⌉ for k ≥ 3 and n ≥ 2k, which exceeds k + 1 for k ≥ 28.

## Gap

Pre-registration issue 13236 records the literature screen: the paper is the only source of the question and its
Theorem 3.5 gives only χ_{ρ,k}(P_n) > k; no later work on it was found in the repository or in web and arXiv
searches.

## Route

1. The vertices whose broadcast reaches the first vertex of the path form a set E; each partition class contributes
   a vertex of E, so |E| ≥ k, and a packing colouring has at most one such vertex of each colour.
2. With d = t − k and m = 8d + 8, the vertices of low colours in E cannot reach vertex m, vertices outside E inside
   [1, t + 1] are few, and every broadcaster beyond t + 1 reaching m has a large colour and is constrained by the
   packing distance against the vertex of the same colour in E.
3. If t ≥ 16d + 13, at most k − 1 vertices reach m, contradicting the k partition classes; hence 15t ≥ 16k − 12.
4. At k = 28 and n = 56, colours at most 29 would require 435 ≥ 436.

## Falsifier

The theorem would fail if some path P_n with n ≥ t + 1 had a packing k-domatic colouring with colours at most t and
15t < 16k − 12.

## Evidence

The proof seat and an independent referee implementation reproduced the paper's small values of χ_{ρ,k}(P_n) by
exhaustive search and checked the arithmetic of the counting lemma.

## Triage

`theorem`; the statement is Problem 2 of arXiv:2610.03477v1, answered negatively.

- Refuted (formalized): χ_{ρ,k}(P_n) ≤ k + 1 fails for k = 28 and n = 56; the counting lemma is formalized for all
  k, n and t.
- Proved (paper): χ_{ρ,k}(P_n) ≥ ⌈(16k − 12)/15⌉ for every k ≥ 3 and n ≥ 2k.
- Open: the exact growth constant of χ_{ρ,k}(P_n) in k; Problem 1 (the least k with χ_{ρ,k}(P_n) > k for all
  n ≥ k) and Problem 3 of the same paper.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv record of arXiv:2610.03477, web, arXiv and GitHub searches and the
repository checks.
