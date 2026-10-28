---
bibkey: hirchegeorgenuradhawilde2026conditional
authors: Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde
year: 2026
title: "Conditional contraction coefficients and their applications to quantum networks"
doi: null
url: https://arxiv.org/abs/2608.27171v1
claim: "For a quantum channel N and a generalized divergence D, the conditional contraction coefficient is η^Δ_D(N) := sup over |R| and ρ_RA ≠ σ_RA of [D((id ⊗ N)(ρ_RA)‖(id ⊗ N)(σ_RA)) − D(ρ_R‖σ_R)] / [D(ρ_RA‖σ_RA) − D(ρ_R‖σ_R)] (Eq. (2.14)), optimized over pairs with a strictly positive finite denominator (Remark 2). The hockey-stick divergence is E_γ(ρ‖σ) := Tr(ρ − γσ)_+ (Eq. (5.1)). For the trace distance (γ = 1), η^c_Tr(N) and η^Δ_Tr(N) are optimized by orthogonal states (Proposition 8). §9 asks whether, for the hockey-stick divergence, the optimization can be restricted to orthogonal states, which would imply monotonicity of the coefficient in γ."
strata_touched:
  - D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction
license: citation-only
triage: anchor
---

# Hirche, George, Nuradha and Wilde, conditional contraction coefficients

C. Hirche, I. George, T. Nuradha and M. M. Wilde, *Conditional contraction coefficients and their applications to quantum networks*, arXiv:2608.27171 [quant-ph] (v1 of 27 August 2026, the only version listed).

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2608.27171v1

No DOI or journal reference is listed in the arXiv metadata. The text was read from the PDF https://arxiv.org/pdf/2608.27171v1:
- p. 8, Definition 2, Eqs. (2.12)–(2.14);
- p. 9, Remark 2;
- p. 37, §5, Eqs. (5.1)–(5.2);
- p. 40, Proposition 8;
- p. 72, §9, the first open problem.

## Source statements

Definition 2 (p. 8): "the conditional contraction coefficient as η∆_D(N) := sup_{|R|, ρRA≠σRA} [D((id ⊗ N)(ρRA)∥(id ⊗ N)(σRA)) − D(ρR∥σR)] / [D(ρRA∥σRA) − D(ρR∥σR)]. (2.14)"

Remark 2 (p. 9): "The optimization is should be over states such that ∞ > D(ρRA∥σRA) − D(ρR∥σR) > 0, which is a strictly stronger constraint than just ρRA ≠ σRA. … As a general rule, in this paper, all ratio optimizations are over strictly positive and finite denominators."

§5 (p. 37): "The hockey-stick divergence is defined as [52] Eγ(ρ∥σ) := Tr(ρ − γσ)+ (5.1) = sup_{0≤M≤I} Tr[M(ρ − γσ)], (5.2) where (A)+ denotes the positive part of a Hermitian matrix A."

Proposition 8 (p. 40): "For a channel N : A → B, the coefficients ηc_Tr(N) and η∆_Tr(N) are optimized by orthogonal states".

§9 (p. 72): "When considering the hockey-stick divergence, can the optimization in the contraction coefficient be restricted to orthogonal states, similar to Proposition 8? This would directly imply that the associated contraction coefficient is monotone in γ, which in turn would have applications similar to the results in [7]."

## Reading used by the repository

The question is read for the conditional coefficient η^Δ_{E_γ} with γ ≥ 1. The complete coefficient η^c is not addressed.

For finite systems A and B and a channel N : A → B, the ratio set S_γ(N) consists of the ratios [E_γ((id ⊗ N)ρ‖(id ⊗ N)σ) − E_γ(ρ_R‖σ_R)] / [E_γ(ρ‖σ) − E_γ(ρ_R‖σ_R)]. These range over every finite reference system R and all density matrices ρ, σ on R ⊗ A with a strictly positive denominator. S^⊥_γ(N) is its subset from pairs with ρσ = 0.

The repository proves two statements:
- S_γ(N) = S^⊥_γ(N) for every γ ≥ 1;
- S_γ(N) = S_δ(N) for all γ, δ ≥ 1, so η^Δ_{E_γ}(N) does not depend on γ ≥ 1.

In the formal numerator, the subtracted reference marginals are taken of the output states (id ⊗ N)ρ and (id ⊗ N)σ; they equal ρ_R and σ_R because N is trace preserving.
