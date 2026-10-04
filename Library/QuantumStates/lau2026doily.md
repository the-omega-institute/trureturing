---
bibkey: lau2026doily
authors: Tony Lau
year: 2026
title: "Beyond the Magic Square Game: Widening the Gap for Two Bell States"
doi: 10.48550/arXiv.2603.20748
url: https://arxiv.org/abs/2603.20748v2
claim: "Section 5 names the candidate classical value 22/25 for the 1/10-synchronous doily game."
strata_touched:
  - D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue
license: citation-only
triage: anchor
---

# Beyond the Magic Square Game: Widening the Gap for Two Bell States

Section 5, p. 20:

> However, it is possible that for p < 1/7, the value of the p-synchronous doily game is less than 31/35. In particular, if Lemma 4.3 can be improved to state that an optimal asymmetric strategy for the doily game wins on at most 12 of 15 synchronous questions, the 1/10-synchronous doily game would have a classical value of 22/25 < 31/35. The author estimates that this could be checked exhaustively using about three years of continuous work on an RTX 4090 graphics card.

Definition 4.1, p. 15:

> For p ∈ [0, 1], the p-synchronous (p-sync) doily game is defined as the nonlocal game ([15], [15], {0, 1}³, {0, 1}³, (1 − p)π₁ + pπ₂, R), for π₁ being the uniform distribution over {(j, k) ∈ [15] × [15] : Eⱼ and Eₖ have exactly one variable in common}, (13) π₂ being the uniform distribution over {(j, j) ∈ [15] × [15] : j ∈ [15]}, (14) and R : [15] × [15] × {0, 1}³ × {0, 1}³ → {0, 1} being the function such that R(j, k, a, b) = 1 if and only if a satisfies the parity of Eⱼ, b satisfies the parity of Eₖ and the bits corresponding to any variables shared between Eⱼ and Eₖ in a are the same as those in b.

Definition 2.2, p. 2:

> For the nonlocal game G = (X, Y, A, B, π, V), a classical deterministic strategy S is any pair of functions S = (A, B) with A : X → A and B : Y → B. A and B will be referred to as Alice’s local strategy and Bob’s local strategy, respectively. Then, the probability that Alice and Bob win G using S is given by the expression Σ_{x∈X, y∈Y} π(x, y)V(x, y, A(x), B(y)). (1)

Section 2, p. 3:

> We may then define the classical value and entangled value of a game G as the supremal probability of winning G over all classical strategies and over all entangled strategies, respectively.

Table 3, p. 6, Boolean equation column:

> E₀ V₀ + V₃ + V₆ = 0; E₁ V₁ + V₃ + V₇ = 0; E₂ V₂ + V₃ + V₈ = 0; E₃ V₀ + V₄ + V₉ = 0; E₄ V₁ + V₄ + V₁₀ = 0; E₅ V₂ + V₄ + V₁₁ = 0; E₆ V₀ + V₅ + V₁₂ = 0; E₇ V₁ + V₅ + V₁₃ = 0; E₈ V₂ + V₅ + V₁₄ = 0; E₉ V₆ + V₁₁ + V₁₃ = 0; E₁₀ V₁₀ + V₁₂ + V₈ = 0; E₁₁ V₁₄ + V₇ + V₉ = 0; E₁₂ V₆ + V₁₀ + V₁₄ = 1; E₁₃ V₁₁ + V₁₂ + V₇ = 1; E₁₄ V₁₃ + V₈ + V₉ = 1.

Addition in these equations is modulo two. Equations and variables retain the
source's zero-based indices and the displayed coordinate order. The source
uniform distributions count ordered intersecting pairs and all fifteen diagonal
questions. Classical strategies choose any of the eight Boolean triples on each
question independently for the two players, including parity-invalid triples.

The exact value at p = 1/10 is addressed by the accompanying Lean result. The
source's conditional suggestion about improving Lemma 4.3 is motivation for that
value; a uniform strengthening of Lemma 4.3 is a separate statement.
