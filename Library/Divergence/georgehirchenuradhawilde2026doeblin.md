---
bibkey: georgehirchenuradhawilde2026doeblin
authors: Ian George; Christoph Hirche; Theshani Nuradha; Mark M. Wilde
year: 2026
title: "Quantum Doeblin Coefficients: Interpretations and Applications"
doi: "10.22331/q-2026-05-22-2115"
url: https://arxiv.org/html/2503.22823v3
claim: "Section 9.2(1) asks whether the complete hockey-stick contraction coefficient satisfies ηᶜ_γ(N) ≤ 1 − α(N), with Hermitian witnesses in Definition 4."
strata_touched:
  - D5/S3/Quantum/Divergence/CompleteHockeyStickDoeblinRefutation
license: citation-only
triage: anchor
---

# Quantum Doeblin coefficients

## Verified locator

Published article DOI 10.22331/q-2026-05-22-2115. The source text used here is arXiv v3, https://arxiv.org/html/2503.22823v3. The relevant locators are Eq. (2.2), Definition 4, Definition 7, Proposition 31 and §9.2(1). [Published article](https://doi.org/10.22331/q-2026-05-22-2115)

## Source statements

Equation (2.2) uses the unnormalized, input-first Choi operator. Definition 4 defines α as the supremum of Tr H over Hermitian H with I ⊗ H ⪯ J. Equation (3.25) requires H ⪰ 0 for α₊. Proposition 31 proves ηᶜ_γ ≤ 1 − α₊ for γ ≥ 1. Section 9.2(1) asks whether ηᶜ_γ ≤ 1 − α. [Equation (2.2)](https://arxiv.org/html/2503.22823v3#S2.E2) · [Definition 4](https://arxiv.org/html/2503.22823v3#Thmdefinition4) · [Equation (3.25)](https://arxiv.org/html/2503.22823v3#S3.E25) · [Proposition 31](https://arxiv.org/html/2503.22823v3#Thmproposition31) · [Section 9.2(1)](https://arxiv.org/html/2503.22823v3#S9.SS2)

`CompleteHockeyStickDoeblinRefutation.result` gives a negative answer at γ = 2. The channel prepares the rays P of (1,0) and Q of (4/5,3/5). Lean identifies its actual Choi blocks and checks the Hermitian minorant H = [[13,6],[6,−3]]/25. Its trace is 2/5 and the reused complete-coefficient lower bound is 9/10, so 1 − α ≤ 3/5 < ηᶜ₂.

For this channel the trace bound is tight. If X is feasible, then X ⪯ P and X ⪯ Q. With u = (1,2) and v = (2,−1), one has `u*Xu ≤ u*Pu = 1` and `v*Xv ≤ v*Qv = 1`. Since `uu* + vv* = 5I`, this gives Tr X ≤ 2/5. The supports of P and Q intersect only at zero, so the only positive semidefinite feasible X is zero. These observations give α = 2/5 and α₊ = 0.

Lluis Eriksson gives an earlier complete Umegaki ratio above the complete trace coefficient for a different binary pure-output channel. The two-profile integral of Hirche and Tomamichel transfers that separation to some γ > 1, because an upper bound at every parameter and in both orientations would also bound the relative-entropy ratio. Eriksson’s complete trace coefficient equals the trace distance between his prepared states P and Q. The feasible Hermitian matrix (P + Q − |P − Q|)/2 has trace one minus that distance, giving a qualitative refutation through the earlier result. The Lean counterexample uses an exact finite witness at γ = 2. [Eriksson v3, §6.4](https://airr.science/papers/ARR-2026-564FZ70CSN83KACD/versions/v3/) · [Hirche and Tomamichel, Corollary 2.3](https://arxiv.org/abs/2306.12343)
