---
bibkey: cheflesjozsawinter2004transformations
authors: Anthony Chefles, Richard Jozsa, Andreas Winter
year: 2004
title: On the existence of physical transformations between sets of quantum states
doi: 10.1142/S0219749904000031
url: https://arxiv.org/abs/quant-ph/0307227
claim: Theorem 2 characterizes a common physical transformation between prescribed pure-state families by a positive semidefinite Hadamard factor between their Gram matrices.
strata_touched:
  - D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame
license: citation-only
triage: anchor
---

# Gram matrices for common quantum state transformations

## Verified locator

Chefles, Jozsa and Winter, *International Journal of Quantum Information* 2(1), 11–21 (2004). Theorem 2 on PDF page 4 of arXiv:quant-ph/0307227 states that a common physical channel maps each prescribed pure input to its prescribed pure output exactly when their Gram matrices satisfy Gₐ = M ∘ Gᵦ for a positive semidefinite factor M. Property 2(i), cited in the theorem, requires diagonal entries one for normalized representatives. The proof obtains the factor from Stinespring environment states, with phase freedom absorbed into the factor. The paper attributes this criterion to antecedent work of Uhlmann and Chefles. [DOI](https://doi.org/10.1142/S0219749904000031) · [ArXiv](https://arxiv.org/abs/quant-ph/0307227) · [Primary PDF, page 4](https://arxiv.org/pdf/quant-ph/0307227#page=4)

## Scope

The cited theorem addresses prescribed pure outputs. The phase-memory guessing problem optimizes one CPTP encoder receiving an unknown quantum signal, allowing mixed memory outputs, and one POVM acting solely on the M-dimensional carrier. Visible encoding supplies the classical label to the encoder. A retained classical branch supplies the decoder with additional information and permits a branch-dependent POVM. The equality proof in this packet derives the rank-one decoder frame and its real normalized virtual Gram from saturation of the guessing bound.

Regula, Fang, Wang and Adesso supply the scalar M-distillation norm and its clipping optimizer. The operational guessing upper bound uses its square divided by the number N of equiprobable labels. Their one-shot pure-state coherence-distillation fidelity uses its square divided by M under the stated classes of coherence operations. The common-channel equality constraints and the Walsh/Fourier comparison concern the guessing problem. [Regula et al., Theorem 4, Eq. (16)](https://arxiv.org/pdf/1711.10512v3#page=4) · [Supplement, Eqs. (S12)–(S13)](https://arxiv.org/pdf/1711.10512v3#page=8)
