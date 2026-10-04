---
bibkey: chanlopezmartinruiz2026rule30
authors: E. Chan-López and A. Martín-Ruiz
year: 2026
title: Symmetric Nonlinear Cellular Automata as Algebraic References for Rule 30
doi: 10.48550/arXiv.2604.00165
url: https://arxiv.org/abs/2604.00165v3
claim: The all-row sign-pattern question of Remark 3 and section 9 for the full-row Rule 30 and Rule 22 support difference.
strata_touched:
  - D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation
license: citation-only
triage: anchor
---

# Rule 30 and the symmetric Rule 22 reference

The source is arXiv:2604.00165v3. Its neighbour convention uses left,
centre and right bits `a,b,c`. Equation (1), p. 3, gives
“g22(a, b, c) = a ⊕ b ⊕ c ⊕ abc.” Proposition 1 on the same page states:
“Rule 30, with ANF g30 = a ⊕ b ⊕ c ⊕ bc, is left-permutive but lacks S3 symmetry.”
XOR is addition and AND is multiplication over the two-element field.

Section 3, p. 4, fixes the configuration evolved “from the single-seed
initial condition η_0 = δ_0”. Definition 2 states: “The support set at time m
is the full-row support S_m = {r ∈ Z : η_m(r) = 1}”. It also specifies:
“All cardinality statements below refer to the full-row set S_m”.
Thus the cardinality counts the entire integer row, including negative
sites and the origin. Equation (11), p. 10, defines
“ϵ(m) = |S_m^(30)| − |S_m^(22)|”. Both supports are finite because the
two rules are quiescent and a single seed has a finite light cone.

Remark 3, p. 11:

> A direct computation for m ≤ 256 shows that ϵ(m) ≤ 0 precisely at the Mersenne indices m = 2^k − 1, with ϵ = 0 for k ≤ 3 and ϵ < 0 for 4 ≤ k ≤ 8.

Section 9, p. 15:

> Is the sign pattern of Remark 3 exact for all k?

The sign-pattern proposition extends the “precisely” biconditional to
every natural index `m ≥ 1`, with Mersenne indices `2^k - 1`, `k ≥ 1`.
The module proves its negation: the two support cardinalities at `m = 767`
are 763 and 768, so the integer difference is −5, although 768 is not a
power of two. This does not refute the finite observation for `m ≤ 256`,
or settle the separate all-Mersenne strict-negativity question. No
resolution of that latter question is asserted here.

## Verified locator

- arXiv v3: https://arxiv.org/abs/2604.00165v3
- DOI: https://doi.org/10.48550/arXiv.2604.00165
