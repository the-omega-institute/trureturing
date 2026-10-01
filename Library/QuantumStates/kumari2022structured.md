---
bibkey: kumari2022structured
authors: A. Kumari; S. Adhikari
year: 2022
title: "Structured negativity: A physically realizable measure of entanglement based on structural physical approximation"
doi: 10.48550/arXiv.2209.03909
url: https://arxiv.org/abs/2209.03909v1
claim: "Negativity is the normalized negative partial-transpose eigenvalue sum; structured negativity is d(d^3+1) max{d/(d^3+1) - lambda_min(SPA-PT(rho)), 0}. The authors conjecture coincidence when q=d(d-1)/2."
strata_touched:
  - D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation
license: citation-only
triage: anchor
---

# Structured negativity

A. Kumari and S. Adhikari, arXiv:2209.03909v1, 2022-09-08, quant-ph;
Annals of Physics 446 (2022) 169113 (journal reference reported on arXiv).
Page numbers below refer to the arXiv v1 PDF.

The abstract (p. 1) states:

> For d ⊗ d dimensional state, we conjecture from the result obtained in this work that negativity coincide with the structured negativity when the number of negative eigenvalues of the partially transposed matrix is equal to d(d−1)/2.

The conclusion (p. 7) states:

> Thus, we conjecture that the negativity and structured negativity coincides when q=d(d−1)/2.

Equation (6), p. 2:

> N(ρ) = (||ρ^{T_B}||_1 − 1)/(d−1) = (2/(d−1)) Σ_{λ_i<0} |λ_i(ρ^{T_B})| where ||.||_1 denotes trace norm and ρ^{T_B} is the partial transposition of the density matrix ρ.

Equation (7), p. 2:

> For d ⊗ d system described by the density operator ρ, the SPA-PT of the state ρ denoted as ρ̃ and it may be expressed as [32],

$$\widetilde\rho = \frac{d}{d^3+1} I\otimes I + \frac{1}{d^3+1}[I\otimes T](\rho).$$

The minimum-eigenvalue convention (p. 3):

> where λ_min(ρ̃) denote the minimum eigenvalue of ρ̃.

Equation (9), p. 3:

> N_S(ρ) = K.max{d/(d^3+1) − λ_min(ρ̃),0} where K = d(d^3+1).

The comparison section (p. 4) states:

> Let us suppose that (I ⊗ T)ρ has q (≤ (d−1)^2) number of negative eigenvalues

The encoding uses matrices indexed by `Fin d × Fin d`, density meaning positive
semidefinite with trace one, and Hermitian eigenvalues counted with multiplicity.
It uses equation (6)'s eigenvalue-sum definition, which the source equates with
the trace-norm definition. No separate Lean trace-norm equivalence is asserted.
The conjecture is universal over d ≥ 2 and density matrices with q=d(d−1)/2.

For ψ=(|00⟩+2|11⟩+2|22⟩)/3, the eigenvalues of the partial transpose of
|ψ⟩⟨ψ| are {1/9,2/9,2/9,−2/9,4/9,4/9,−2/9,−4/9,4/9}. Thus q=3,
N=8/9, λ_min(ρ̃)=23/252, and N_S=4/3. The Lean result refutes the conjecture
with this pure state. The spectral identification uses Mathlib's characteristic
polynomial roots and Hermitian spectral theorem, including multiplicity.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2209.03909
- URL: https://arxiv.org/abs/2209.03909v1
- PDF read: https://arxiv.org/pdf/2209.03909v1 (abstract p. 1;
  equations (6), (7) p. 2; equation (9) p. 3; q convention p. 4;
  conclusion p. 7).
