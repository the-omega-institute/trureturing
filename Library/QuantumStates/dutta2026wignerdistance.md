---
bibkey: dutta2026wignerdistance
authors: Soumyojyoti Dutta; Tushar
year: 2026
title: "A Phase-Space Geometric Measure of Magic in Qubit Systems"
doi: 10.48550/arXiv.2603.20792
url: https://arxiv.org/abs/2603.20792v3
claim: "Conjecture 5.5 asks that for equatorial magic ρ and qubit σ with s(σ) > 0 the tensor deficit factor as C(ρ)·f(σ) for a universal f; Conjecture 5.6 asks for equatorial multiplicativity of the qubit Wigner distance; Conjecture 5.7 asks for self-tensor superadditivity on the nonpositive Bloch-product branch."
strata_touched:
  - D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules
  - D5/S3/Quantum/Magic/QubitWignerDeficitFactorRefutation
license: citation-only
triage: anchor
---

# A Phase-Space Geometric Measure of Magic in Qubit Systems

Soumyojyoti Dutta and Tushar, arXiv:2603.20792v3 [quant-ph]. Page numbers
refer to the printed PDF. The frame is the Wootters product frame.

Page 3, Section 2.1:

> The $n$-qubit Pauli group $\mathcal{P}_n$ consists of $n$-fold tensor
> products of $\{I, X, Y, Z\}$ with phases $\{\pm1, \pm i\}$.

> A stabilizer state is the unique $+1$ eigenstate of an abelian subgroup
> $S \leq \mathcal{P}_n$ of size $2^n$.

Page 3, Section 2.3:

> The single-qubit phase-point operators are indexed by
> $\alpha_k = (q_k, p_k) \in \mathbb{F}_2^2$:
> $A_{(q_k,p_k)} = \tfrac{1}{2}\!\bigl(I + (-1)^{p_k} X + (-1)^{q_k+p_k} Y + (-1)^{q_k} Z\bigr)$.

> For $n$ qubits, $A_\alpha = A_{\alpha_1} \otimes \cdots \otimes A_{\alpha_n}$,
> and the discrete Wigner function is
> $W_\rho(\alpha) = \frac{1}{2^n}\,\tr(\rho\,A_\alpha)$.

Page 3, Section 3.1 and Definition 3.1:

> The stabilizer Wigner polytope is
> $\mathcal{W}_{\mathrm{free}} := \mathrm{conv}\{W_\sigma : \sigma \in \mathrm{Stab}_n\} \subset \mathbb{R}^{4^n}$.

> $C(\rho) := \min_{W_f \in \mathcal{W}_{\mathrm{free}}}\|W_\rho - W_f\|_1$.

Page 7, Observation 5.1:

> For a single-qubit state $\rho$ with Bloch vector $\vec r$, write
> $s(\rho) := \operatorname{sgn}(r_x r_y r_z)$.

Version 4 (arXiv:2603.20792v4, revised 6 October 2026), Section 5.2, Figure 1 caption and Section 5.4
(`main.tex` lines 1009, 1093 and 1146–1155); Conjecture 5.5 has the same wording in v3:

> Let $\rho_T$ denote any equatorial single-qubit magic state;

> Deficit $(1+C(\rho))(1+C(\sigma))-1-C(\rho\otimes\sigma)$ against $C(\rho)C(\sigma)$ for Haar-random pure single-qubit pairs

> \begin{conjecture}[Factored deficit] For equatorial magic states $\rho$ and qubit states $\sigma$ with $s(\sigma) > 0$: $\mathrm{deficit}(\rho,\sigma) = C(\rho)\cdot f(\sigma)$ for a universal function $f\geq0$ of the Pauli invariants $(|r_x|,|r_y|,|r_z|)$ of $\sigma$, vanishing iff $s(\sigma)\leq0$. \end{conjecture}

Page 8, Conjecture 5.6 (Equatorial multiplicativity):

> For $\langle Z\rangle_\rho = \langle Z\rangle_\sigma = 0$:
> $C(\rho \otimes \sigma) = C(\rho) + C(\sigma) + C(\rho)C(\sigma)$.

Page 8, Conjecture 5.7 (Self-tensor superadditivity, $s\leq0$ branch):

> For any qubit state $\rho$ with $s(\rho)\leq 0$:
> $C(\rho \otimes \rho) \geq 2C(\rho)$.

The encoding uses positive semidefinite complex matrices of trace one,
`Fin 2 × Fin 2` for phase points, and actual commuting subgroups of the
matrix unitary group for stabilizer states. Unique eigenstates mean
normalized eigenrays; their density matrices are `vecMulVec ψ (star ψ)`.
The real part in the Wigner transform agrees with its real-valued trace
on Hermitian states. The distance is represented by the infimum of the
same finite-coordinate absolute-value errors; `WignerDistanceMinimum.COne_min`
and `CTwo_min` prove that this is the source minimum for every matrix.
The equatorial proof constructs an attaining stabilizer mixture; the
self-tensor proof bounds that minimum. The condition $s(\rho)\leq0$ is encoded as
$r_xr_yr_z\leq0$, including the zero branch.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2603.20792
- URL: https://arxiv.org/abs/2603.20792v3
- URL: https://arxiv.org/abs/2603.20792v4 (latest version; Conjecture 5.5 and Conjectures 5.6, 5.7 unchanged)
