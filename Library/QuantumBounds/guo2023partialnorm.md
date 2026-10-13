---
bibkey: guo2023partialnorm
authors: Y. Guo
year: 2023
title: "Partial-Norm of Entanglement: Entanglement Monotones That are not Monogamous"
doi: 10.1088/1367-2630/acf152
url: https://arxiv.org/abs/2212.06521v6
claim: "The partial negativity of a pure state with decreasing Schmidt coefficients λ₁ ≥ λ₂ ≥ ⋯ is λ₁λ₂, with reduced function ĥ(ρ) = √(δ₁δ₂) for the two largest eigenvalues of the reduced state; the paper conjectures that ĥ is concave."
strata_touched:
  - D5/S3/Quantum/Entanglement/PartialNegativityConcavityRefutation
license: citation-only
triage: anchor
---

# Guo, Partial-Norm of Entanglement: Entanglement Monotones That are not Monogamous

Y. Guo, *Partial-Norm of Entanglement: Entanglement Monotones That are not Monogamous*,
New J. Phys. 25 (2023) 083047; arXiv:2212.06521v6 (31 August 2023; quant-ph).

## Verified locator

DOI: 10.1088/1367-2630/acf152.
Primary version read: https://arxiv.org/abs/2212.06521v6 (the last arXiv version).
The TeX source of v6 supplies the definition of concavity of a reduced function (Eq. `h`), the
ordering of the Schmidt coefficients, Proposition 1 (`pro1`), the definition of the partial
negativity with its reduced function, the conjecture and reference [Suppl].

## Source statements

The source macros `\ra`, `\la`, `\mH`, `\mS` are written out.

Concavity: "$h[\lambda\rho_1+(1-\lambda)\rho_2]\geq\lambda h(\rho_1)+(1-\lambda)h(\rho_2)$ for any states $\rho_1$, $\rho_2$, and any $0\leq\lambda\leq1$."

Schmidt ordering: "Let $|\psi\rangle=\sum_{j=1}^r\lambda_j|e_j\rangle^A|e_j\rangle^B$ be the Schmidt decomposition of $|\psi\rangle\in\mathcal H^{AB}$, where $\lambda_1\geq\lambda_2\geq\cdots\geq\lambda_r$, and $r$ is the Schmidt rank of $|\psi\rangle$."

Proposition 1: "Let $E$ be an entanglement measure with the reduced function $h$ defined as Eq. (h). If $E$ is an entanglement monotone, then $h$ is concave."

Partial negativity: "Then $\hat{N}(|\psi\rangle)=\lambda_1\lambda_2$, and the corresponding reduced function is $\hat{h}(\rho^A)=\sqrt{\delta_1\delta_2}$, where $\delta_1=\lambda_1^2$, $\delta_2=\lambda_2^2$."

Conjecture: "We conjecture that $\hat{h}$ is concave [Suppl]. $\hat{h}$ is strictly concave on $\mathcal S(\mathcal H)$ with $\dim\mathcal H=2$ since it reduced to an elementary symmetric function, but it is not true for the higher dimensional case."

Reference [Suppl]: "We checked by many examples that it is true. Especially, if $[\rho, \sigma]=0$, $\hat{h}(\rho/2+\sigma/2)\geq\hat{\rho}/2+\hat{h}(\sigma)/2$ is always true."

After the conjecture: "We now assume that $\hat{N}$ is an entanglement monotone, then we can conclude the following."

## Scope

The paper studies entanglement monotones whose reduced functions depend on part of the spectrum of the reduced state (partial norms) and shows that several are not monogamous. Y. Guo, *Complete Genuine Multipartite Entanglement Monotone*, arXiv:2301.00334v3 (Results in Physics 57 (2024) 107430), restates $\hat h(\rho)=\sqrt{\delta_1\delta_2}$ with "$\delta_1$, $\delta_2$ are the two largest eigenvalues of $\rho$", repeats the conjecture and assumes the concavity of $\hat h$ in its later sections.
