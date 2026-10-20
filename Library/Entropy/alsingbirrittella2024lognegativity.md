---
bibkey: alsingbirrittella2024lognegativity
authors: P. M. Alsing; R. J. Birrittella
year: 2024
title: "Numerical Evidence for a Bipartite Pure State Entanglement Witness from Approximate Analytical Diagonalization"
doi: 10.3390/foundations5020019
url: https://arxiv.org/abs/2404.13725v1
claim: "Equation (22) numerically supports the logarithmic-negativity sandwich for positive Hermitian amplitude ensembles and upper equality for real amplitudes."
strata_touched:
  - D5/S3/Quantum/Information/AlsingBirrittellaLogNegativitySandwich
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.3390/foundations5020019

Source: https://arxiv.org/abs/2404.13725v1

# The Alsing–Birrittella logarithmic-negativity sandwich

The source is arXiv:2404.13725v1; the journal citation is *Foundations* 5(2)
(2025), 19. The arXiv PDF and TeX supply the statements below. The journal DOI
is supplied by the literature screen; its publisher text is unverified.

The introduction, p. 1, calls logarithmic negativity

> A widely used “measure” of entanglement for both pure and mixed states, both discrete and continuous variable, is the Log Negativity (LN)

and gives $LN(\rho_{ab})=\log_2(1+2N)$, followed by

> where the negativity N is given by the sum of the absolute values of the negative eigenvalues of the partial transpose of ρ_ab.

Equation (11a), p. 4, defines

$$N_a(|\psi\rangle_{ab}) := \frac12\sum_n\sum_{m\ne n}
\left|\operatorname{Det}\begin{pmatrix}c_{nn}&c_{nm}\\c_{mn}&c_{mm}\end{pmatrix}\right|.$$

Equation (11b) defines $LN_a(|\psi\rangle_{ab}) := \log_2(1+2N_a)$.
Equations (17b)–(17c), p. 8, give the mixed-state expressions

$$N_a\to\frac12\sum_{n,m\ne n}|\rho_{nn,mm}-\rho_{nm,mn}|,
\qquad LN_a=\log_2(1+2N_a).$$

Both are half-sums over ordered unequal pairs. Exact logarithmic negativity is
$LN_e(\rho)=\log_2\|\rho^\Gamma\|_1$, with partial transposition on the second
factor. The ensemble average is $\mathcal{LN}_a^{avg}=\sum_i p_i LN_a(|\psi_i\rangle)$.

Section IV, p. 11, Equation (22), states:

> we have numerically found that 𝓛𝓝_a^avg(ρ_ab) ≤ LN_e(ρ_ab) ≤ LN_a(ρ_ab) when the mixed state is written as a pure state decomposition (PSD) ρ_ab = Σ_i p_i |ψ_i⟩⟨ψ_i|, and in addition the quantum amplitude matrix C_i of each pure state component |ψ_i⟩ = Σ_nm C_i,nm |n,m⟩ is uniformly generated (over the Haar measure) as a positive Hermitian matrix, C_i = C_i† ≥ 0.

> Further, we find that the second inequality is surprisingly saturated, i.e. LN_e(ρ_ab) = LN_a(ρ_ab) in Eq.(22), if the uniformly randomly generated C_i matrices above are real, i.e. C_i = C_i^T.

The finite-dimensional formulation uses arbitrary positive semidefinite complex
amplitudes with $\operatorname{tr}(C_iC_i^\dagger)=1$ and nonnegative weights
summing to one. It therefore includes the sampled class. Hermitian amplitudes
are real exactly when they are transpose symmetric. No common eigenbasis or
pairwise commutation assumption is imposed. The general pure-state witness
question for arbitrary amplitude matrices is outside this statement.

The literature screen in issue #19208 found no settlement in its checked arXiv,
journal, citation-index and later-author records. Completeness is
ASSUMED-UNVERIFIED. This note incorporates no source software.
