---
bibkey: hertz2025lossbeamsplitters
authors: Anaelle Hertz, Noah Lupu-Gladstein, Khabat Heshami, Aaron Z. Goldberg
year: 2026
title: "Equalities and inequalities from entanglement, loss, and beam splitters"
doi: 10.1007/s40509-026-00402-0
url: https://arxiv.org/abs/2501.02047v1
claim: "For the vacuum-environment loss channel ρ_T = Tr₂[B(T)(ρ₁ ⊗ |0⟩⟨0|)B(T)†], the paper proves convexity of the purity in the transmission T and conjectures that it is log-convex on [0, 1] for every state (Conjecture 7, equivalently inequality (26)); Appendix B extends the conjecture to mixtures of identical two-copy states (Conjecture 19, (B4))."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation
license: citation-only
triage: anchor
---

# Hertz–Lupu-Gladstein–Heshami–Goldberg, equalities and inequalities from entanglement, loss, and beam splitters

A. Hertz, N. Lupu-Gladstein, K. Heshami and A. Z. Goldberg, *Equalities and inequalities from entanglement, loss, and beam splitters*, arXiv:2501.02047v1 [quant-ph] (3 January 2025); Quantum Studies: Mathematics and Foundations **13**, 34 (1 August 2026), DOI 10.1007/s40509-026-00402-0.

## Verified locator

DOI: 10.1007/s40509-026-00402-0 (Quantum Stud. Math. Found. 13, article 34, published 1 August 2026, CC BY 4.0, from Crossref metadata; the journal text was not read: the publisher page and PDF redirect to an authorization step).
Primary version read: https://arxiv.org/abs/2501.02047v1 (the only arXiv version).
Source: https://arxiv.org/pdf/2501.02047v1 (text read from the PDF):
- §I.A, the beam splitter B(T) and the loss channel;
- §III, Corollary 6 and Conjecture 7 with the equivalent inequality (26);
- Appendix B, "Evidence for log-convexity of the purity", with (B1) and Conjecture 19 (B4).

## Source statements

§I.A: the beam splitter is B(T) = exp(arccos(√T)(a₁a₂† − a₁†a₂)), and a state ρ₁ subject to loss is ρ_T = Tr₂[B(T)(ρ₁ ⊗ |0⟩⟨0|)B(T)†], with transmission probability T ∈ [0, 1].

§III: "a bounty of evidence suggests that a much stronger property holds: the logarithm of the purity appears also to be convex in T ∈ [0, 1]. Equivalently, the order-2 Renyi entropy appears to be concave, which leads us to the following conjecture: Conjecture 7. The purity of a state ρ₁ subject to loss is log-convex in T ∈ [0, 1]; ∂² log Tr[ρ_T²]/∂T² ≥ 0. Conjecture 7 can equivalently be written as (∂/∂T Tr[ρ_T²])² ≤ Tr[ρ_T²] ∂²/∂T² Tr[ρ_T²]. (26)" … "The problem of log-convexity with respect to the original loss parameter T is harder and despite a multitude of evidence, we do not yet have a proof."

Appendix B: "preliminary numerical evidence suggests that the expression Tr[Φ(1−2T)^{N−}] is log-convex for T ∈ [0, 1] whenever Φ can be expressed as a convex combination of states of the form ρ₁⊗ρ₁. This leads us to the following conjecture. Conjecture 19 (Unfairness witness). For any state of the form Φ = Σ_i P_i ρ_i⊗ρ_i, where ρ_i ⪰ 0, P_i ≥ 0, Σ_i P_i = 1 and any λ ∈ [−1, 1], Tr[Φλ^{N−}] Tr[Φλ^{N−−2}N−(N− − 1)] ≥ Tr[Φλ^{N−−1}N−]². (B4)"
