---
bibkey: songchendjokovic2023uniquebasis
authors: Zhiwei Song, Lin Chen and Dragomir Z. Djokovic
year: 2024
title: "The existence of distinguishable bases in three-dimensional subspaces of qutrit-qudit systems under one-way local operations and classical communication"
doi: 10.1109/TIT.2024.3435412
url: https://arxiv.org/abs/2307.01980v3
claim: "Eqs. (2)–(3) define a qutrit-qudit subspace; p. 3 asks whether every mixed state supported there has the EOF of the pure state |Ψ₁⟩."
strata_touched:
  - D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1109/TIT.2024.3435412

Source: https://arxiv.org/abs/2307.01980v3

IEEE Transactions on Information Theory 70(12), 8806–8815 (2024).
The equation and page locators below refer to arXiv version 3.

## Source objects

Eq. (2) gives the 9 × 9 matrix G. Its nonzero entries, in one-based
row and column notation, are (1,1)=2/3, (2,2)=1/√3,
(2,6)=i/(3√3), (2,7)=2/(3√3), (3,3)=√2/3,
(4,4)=1/√3, (5,5)=√2/3, (6,6)=√11/(3√3),
(6,7)=(3+2i)/(3√33), (7,7)=1/√33, (8,8)=2/3,
and (9,9)=1/√3. All other entries vanish.

Eq. (3) reads:

> |Ψ₁⟩ = |1⟩⊗|r₁⟩ + |2⟩⊗|r₄⟩ + |3⟩⊗|r₇⟩,
> |Ψ₂⟩ = |1⟩⊗|r₂⟩ + |2⟩⊗|r₅⟩ + |3⟩⊗|r₈⟩,
> |Ψ₃⟩ = |1⟩⊗|r₃⟩ + |2⟩⊗|r₆⟩ + |3⟩⊗|r₉⟩,

> where |r_i⟩ is the i-th column vector of G

The coordinate encoding uses zero-based Fin indices. The pair (a,b)
represents |a⟩⊗|b⟩, so Ψ_k(a,b)=G(b,3a+k).
Square roots are nonnegative real square roots embedded into ℂ.
The subspace S is the complex span of the three vectors.

## Question

Page 3 states:

> Further, by calculation one can see that every state in the span of the three states has entanglement more than 1.52 ebits. Hence, the entanglement of formation (EOF) of every mixed state whose range is contained in the span is also more than 1.52 ebits [19]. We don't know whether this EOF is exactly equal to that of the pure state |Ψ₁⟩.

EOF is encoded by FormationBounds.E_F, the infimum of finite-ensemble
costs with marginal entropy in bits. The question is the universal equality
for positive semidefinite trace-one matrices whose range lies in S.
The pure state on its right side is rankOneDensity(Psi 0).

## Refutation and boundary

The repository refutes that equality using ρ₀=(P₁+P₂+P₃)/3.
The superpositions (Ψ₁±√3 Ψ₂)/2 have marginal eigenvalues
(17,10,9)/36. An ensemble with their weights 2/9 each, followed by
Ψ₁ with weight 2/9 and Ψ₃ with weight 1/3, averages to ρ₀.
Its cost is strictly below the pure-state entropy H(4/9,1/3,2/9).
The exact strict inequality follows from 2¹⁰² < 17¹⁷·5¹⁰·3⁶.

The exact infimum for ρ₀ and the general positive diagonal-weight family
are not established by this module. The entropy upper bound is compatible
with the source's lower bound of 1.52 ebits and does not refute it.
The source's other distinguishability results do not depend on equality
of these EOF values.

## Literature boundary

The inherited screen covered 19 full texts, including later Song–Chen
papers and Xu–Nie–Sun, arXiv:2501.05237; it found no answer to this
question. That is a bounded search result, not a complete priority claim.
The journal paragraph is unread because the IEEE response supplied no text
and Firecrawl returned HTTP 402. Completeness is ASSUMED-UNVERIFIED.
