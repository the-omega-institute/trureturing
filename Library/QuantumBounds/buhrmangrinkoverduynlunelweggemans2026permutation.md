---
bibkey: buhrmangrinkoverduynlunelweggemans2026permutation
authors: Harry Buhrman; Dmitry Grinko; Philip Verduyn Lunel; Jordi Weggemans
year: 2026
title: "Permutation tests for quantum state identity"
doi: null
url: https://arxiv.org/abs/2405.09626v2
claim: "For a subgroup G of S_n the G-test measures Π_G = (1/|G|) Σ_{π∈G} ψ(π) (Eqs. (61)–(62)); it has completeness 1 (Eq. (63)) and soundness P^G_s(µ) = 1 − (1/(n choose µ)) Σ_λ K_{λ,µ} r^G_λ (Eq. (65)). For G = S_n, Theorem 5 gives the threshold prior p∗(µ) = 1/(1 + (n choose µ)) below which the trivial test is optimal. §6 leaves open the threshold prior p∗(G, µ) below which the trivial test outperforms the G-test."
strata_touched:
  - D5/S3/Quantum/Measurements/GTestThresholdPrior
license: citation-only
triage: anchor
---

# Buhrman, Grinko, Verduyn Lunel and Weggemans, permutation tests for quantum state identity

H. Buhrman, D. Grinko, P. Verduyn Lunel and J. Weggemans, *Permutation tests for quantum state identity*, arXiv:2405.09626 [quant-ph] (v2 of 14 April 2026; v1 of 15 May 2024).

## Verified locator

No DOI or journal reference is listed in the arXiv metadata.
Primary version read: https://arxiv.org/abs/2405.09626v2.
Source: https://arxiv.org/pdf/2405.09626v2 (text read from the PDF):
- Definition 1, the quantum state identity problems;
- §4.1.1, Eqs. (11)–(13) and Lemma 1;
- §4.1, the Bayesian success probability and Theorem 5;
- §4.2, Eqs. (61)–(65), the G-test;
- §6, Discussion and open problems.

## Source statements

§4.1.1: "ρ^µ_≠ := ∫ U^{⊗n} |1^{µ1} 2^{µ2} … d^{µd}⟩⟨1^{µ1} 2^{µ2} … d^{µd}| (U†)^{⊗n} dU, (11) ρ̃^µ_≠ := (1/n!) Σ_{π∈S_n} ψ(π) ρ^µ_≠ ψ(π^{−1}), (12) ρ^n_= := ∫ U^{⊗n} |1^n⟩⟨1^n| (U†)^{⊗n} dU, (13) where µ ⊢ n is some partition of n with µ_2 > 0".

§4.2: "Assuming that we want to distinguish between ρ̃^µ_≠ and ρ^n_=, we call the G-test the measurement given by Π_= = Π_G, Π_≠ = 1 − Π_G, (61) where Π_G is the projector onto the trivial irrep of G: Π_G := (1/|G|) Σ_{π∈G} ψ(π). (62)" The completeness is P^G_c(µ) = 1 (63), and "the soundness probability of the G-test can be calculated to be P^G_s(µ) = 1 − (1/(n choose µ)) Σ_{λ⊢_d n} K_{λ,µ} r^G_λ, (65) where r^G_λ is the multiplicity of the trivial irrep of the subgroup G ⊆ S_n inside the irrep λ of the symmetric group S_n."

§4.1, symmetric setting: "In the Bayesian (or symmetric) setting with prior {p, 1 − p}, one maximises the average success probability P_succ = p P_c + (1 − p) P_s = 1 − pα − (1 − p)β. Theorem 5 fully solves this: the permutation test (α = 0, β = 1/(n choose µ)) is optimal for p ≥ p∗(µ), and the trivial test (α = 1, β = 0) is optimal for p ≤ p∗(µ)."

§6: "A further open question is to determine, for a given subgroup G and partition µ, the threshold prior p∗(G, µ) below which the trivial test outperforms the G-test, analogous to the threshold p∗(µ) established for the permutation test in Theorem 5."

## Reading used by the repository

Tensors of n qudits are functions on words `Fin n → Fin d`, and ψ(π) permutes positions. A word w of multiplicities µ, with at least two values, stands for the source's 1^{µ1} 2^{µ2} … d^{µd}; its S_n-orbit is the set W_µ of words with these multiplicities, of size M = n!/∏_i µ_i!. O is the number of G-orbits on W_µ. For a fixed unitary U, ρ̃ is Eq. (12) applied to U^{⊗n}|w⟩⟨w|(U†)^{⊗n}; the tested traces do not depend on U, so they agree with the Haar mixture of Eq. (11). The question of §6 is read as: determine p∗(G, µ) such that the G-test has larger Bayesian success probability than the trivial test exactly when p > p∗(G, µ).
