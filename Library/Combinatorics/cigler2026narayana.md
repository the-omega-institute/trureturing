---
bibkey: cigler2026narayana
authors: Johann Cigler
year: 2026
title: "Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1"
doi: 10.48550/arXiv.2608.03363
url: https://arxiv.org/abs/2608.03363v2
claim: "Weighted bounded Dyck paths with Narayana weights and q = -1 weights; Conjecture 2 (a finite-height product formula) and Conjecture 3 (expansions in even strips)."
strata_touched:
  - D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansion
license: citation-only
triage: anchor
---

# Cigler, Narayana polynomials and q-Narayana polynomials for q = −1

A Dyck path uses up-steps and down-steps and never goes below height 0; a down-step from height k + 1 to height k
carries the weight τ_k and an up-step the weight 1. With τ = (1, t, 1, t, …) the weighted count of Dyck paths of
semilength n is the Narayana polynomial C_n(t); with τ = (1, t, −1, −t, 1, t, −1, −t, …) it is the q-Narayana
polynomial c_n(t) = C_n(t; −1). Restricting to the strip 0 ≤ y ≤ h gives C_n^{(h)}(t) and c_n^{(h)}(t); the
unrestricted identity c(t, z) c(−t, −z) = C(t², z²) is the paper's equation (6).

Section 4 states two conjectures for bounded paths:

- Conjecture 2, equation (79) (Conjecture 1, equation (62), in v1): for m ≥ 1,
  C^{(4m)}(t², z²) = c^{(4m)}(t, z) c^{(4m)}(−t, −z) and C^{(4m+1)}(t², z²) = c^{(4m+1)}(t, z) c^{(4m+1)}(−t, −z).
- Conjecture 3 (Conjecture 2 in v1): for m ≥ 1 and n ≥ 0,
  C_{n+1}^{(2m)}(t) = Σ_j C_j^{(m−1)} binom(n, 2j) t^j (1 + t)^{n−2j} and
  c_{n+1}^{(2m)}(t) = Σ_j (−1)^j C_j^{(m−1)} binom(⌊n/2⌋, j) t^j (1 + t)^{n−2j}, where C_j^{(m−1)} is the number of
  Dyck paths of semilength j in the strip of height m − 1.

The module `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansion` proves Conjecture 3.

## Verified locator

DOI: 10.48550/arXiv.2608.03363

URL: https://arxiv.org/abs/2608.03363v2

- Locator: Section 4, Conjecture 3, expansion formulas for C_{n+1}^{(2m)}(t) and c_{n+1}^{(2m)}(t).
- Locator: Section 4, Conjecture 2, equation (79), the product formula for heights 4m and 4m + 1.
- Locator: Section 1, equation (6), the unrestricted product identity.
