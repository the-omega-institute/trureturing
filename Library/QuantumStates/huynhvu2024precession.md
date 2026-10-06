---
bibkey: huynhvu2024precession
authors: Khoi-Nguyen Huynh-Vu; Lin Htoo Zaw; Valerio Scarani
year: 2024
title: "Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum"
doi: null
url: https://arxiv.org/abs/2311.00806
claim: "Conjecture 2, Eq. (32): for the precession protocol and spins {1, K/2} with K ≥ 7, Psep_K({1, K/2}) = ½ [1 + 2^{−(K−1)} binom(K−1, (K−1)/2) (K−1)/(K+1)]."
strata_touched:
  - D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound
license: citation-only
triage: anchor
---

# Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum

Khoi-Nguyen Huynh-Vu, Lin Htoo Zaw and Valerio Scarani, arXiv:2311.00806v2 (2024), *Certification of genuine multipartite entanglement in spin ensembles with measurements of total angular momentum*.

The paper defines the precession protocol by

> Jk := e^{−i(2πk/K)Jz/ℏ} Jx e^{i(2πk/K)Jz/ℏ} = cos(2πk/K)Jx + sin(2πk/K)Jy, where k ∈ {0, 1, . . . , K − 1}.

Equations (2)–(3) state

> PK := (1/K) Σ_{k=0}^{K−1} [Pr(Jk > 0) + ½ Pr(Jk = 0)],
>
> QK := (1/K) Σ_k pos(Jk),
>
> Here, pos(Jk) is defined on the eigenstates |j, m⟩k of Jk, such that Jk|j, m⟩k = ℏm|j, m⟩k and 2 pos(Jk)|j, m⟩k = [1+sgn(m)]|j, m⟩k, with the usual convention sgn(0) = 0.

Conjecture 2 (Eq. (32), §III, PDF p. 8) is:

> The separable bound for {ȷ̃, ȷ̃′} = {1, K/2} with K ≥ 7 is Psep_K({1, K/2}) = ½ [1 + 2^{−(K−1)} binom(K−1, (K−1)/2) (K−1)/(K+1)].

The formalization uses the standard descending |j,m⟩ basis with ℏ = 1, total angular momentum J = J^(1) ⊗ I + I ⊗ J^(K/2), and the product-pure form of the separable maximum. Hermitian spectral projection uses Mathlib’s `Matrix.IsHermitian.cfc` with the source’s positive weight, including half weight at zero; the finite spectrum requires no continuity hypothesis.

## Verified locator

https://arxiv.org/abs/2311.00806v2. Eqs. (1)–(3): PDF p. 2; Conjecture 2 and Eq. (32): §III, PDF p. 8; the separable maximum is specified in Eqs. (7) and (10).
