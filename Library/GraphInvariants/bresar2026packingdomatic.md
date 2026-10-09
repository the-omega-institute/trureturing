---
bibkey: bresar2026packingdomatic
authors: Boštjan Brešar, Jasmina Ferme, Wenjie Hu
year: 2026
title: "Partitioning an S-packing coloring into broadcast dominating sets"
doi: 10.48550/arXiv.2610.03477
url: https://arxiv.org/abs/2610.03477v1
claim: "Introduces packing k-domatic colourings and the invariant χ_{ρ,k}; proves χ_{ρ,k}(P_n) > k for k ≥ 12 and n ≥ k (Theorem 3.5) and asks in Problem 2 whether χ_{ρ,k}(P_n) ≤ k + 1 for k ≥ 3 and n ≥ 2k."
strata_touched:
  - D5/S3/Combinatorics/PackingDomatic/PackingDomaticPath
license: citation-only
triage: anchor
---

# Brešar, Ferme and Hu, packing k-domatic colourings

A packing k-domatic colouring of a graph G uses colours in [t], keeps two vertices of colour j at distance greater
than j, and admits a partition of V(G) into k classes each of which dominates every vertex x by broadcasting: some a
in the class satisfies d(x, a) ≤ f(a). The least such t is χ_{ρ,k}(G). For paths the paper shows χ_{ρ,k}(P_n) = k
for small k and large n, and χ_{ρ,k}(P_n) > k for k ≥ 12 and n ≥ k (Theorem 3.5). Section 5 asks: "Problem 2. Is it
true that χ_{ρ,k}(P_n) ≤ k + 1 for any k ≥ 3 and any n ≥ 2k?"

The module `D5/S3/Combinatorics/PackingDomatic/PackingDomaticPath` answers Problem 2 negatively.

## Verified locator

DOI: 10.48550/arXiv.2610.03477

URL: https://arxiv.org/abs/2610.03477v1

- Locator: Section 1 (definitions); Section 3, Theorem 3.5; Section 5, Problem 2.
