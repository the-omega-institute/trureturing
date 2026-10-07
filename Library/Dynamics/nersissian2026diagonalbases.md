---
bibkey: nersissian2026diagonalbases
authors: Tigran Nersissian
year: 2026
title: Diagonal Bases and Diagonal Periods of Elementary Cellular Automata
doi: 10.48550/arXiv.2609.25078
url: https://arxiv.org/abs/2609.25078v1
claim: Definition 1 fixes the canonical polynomial lift and orbit; Remark 6 and Section 19 leave the Rule 84 modulo-three center-column pattern without an all-time proof.
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn
license: citation-only
triage: anchor
---

# Diagonal bases and diagonal periods of elementary cellular automata

Definition 1, page 4 of arXiv:2609.25078v1, defines the unique multilinear
algebraic normal form over F₂ and lifts its coefficients to {0, 1} in ℤ.
It states:

> The variables a, b, c are the left, center and right neighbors.

> For an initial condition c₀ = (c₀(0), c₀(1), …) placed at x = 0, 1, … on a zero background, write A_{R,c₀}(t, x), t ≥ 0, x ∈ Z, for the orbit under p_R.

Remark 6, page 12, states:

> (The outstanding Rule 84 case) The polynomial of Rule 84 is (a + b + ab)(1 + c). Modulo three, its center column begins 1, 1, 2, 2, 1, 2, 2, … and follows the repeating block (1, 2, 2) after the first entry for the tested times 0 ≤ t < 2048. All center values are also units modulo 9 and 27 on that range, as Corollary 2 predicts. An all-time proof of the observed pattern is not supplied here. If Rule 84 is universal modulo three, it is universal at every power of three; three could not be the sole exceptional modulus.

Section 19, page 42, states:

> The classification reduces the remaining single-seed universality question to the eight rules in E at odd primes. The observed Rule 84 pattern modulo three requires an invariant or an all-time recurrence proof. A finite nonzero prefix is insufficient.

The Lean orbit uses the modulus 3 and single seed δ₀, with synchronous
updates on the whole integer lattice. Its local polynomial is exactly
$(a+b+ab)(1+c)$ in `ZMod 3`. The all-time statement includes time zero
and all three positive-time residue classes.

Corollary 1, page 10, identifies all-window diagonal-basis universality
with triangularity and unit center values. Corollary 2, page 11, transfers
universality modulo a prime to every positive power of that prime, using
the compatibility of the integer polynomial update with reduction.
These are source results; the module proves the modulo-three pattern.
It does not formalize prime-power transfer or the remaining odd-prime cases.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2609.25078
- arXiv v1: https://arxiv.org/abs/2609.25078v1
- PDF: https://arxiv.org/pdf/2609.25078v1
- Definition 1: page 4; Remark 6: page 12; Section 19: page 42.
