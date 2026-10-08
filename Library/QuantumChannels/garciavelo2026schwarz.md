---
bibkey: garciavelo2026schwarz
authors: A. García-Velo, A. Ibort
year: 2026
title: "Schwarz maps with symmetry"
doi: 10.48550/arXiv.2601.02282
url: https://arxiv.org/abs/2601.02282v1
claim: "Remark V.2: the eigenvalues of the Choi matrix of a unital, Hermiticity-preserving U(n₁)⊗U(n₂)-equivariant map are the four values of Lemma V.8 with multiplicities 1, n₁²−1, n₂²−1 and (n₁²−1)(n₂²−1); Lemma V.8 states them only for n₁, n₂ ∈ {2, 3}, and the general case is stated as a conjecture."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum
  - D5/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared
license: citation-only
triage: anchor
---

# García-Velo and Ibort, Schwarz maps with symmetry

A. García-Velo and A. Ibort, *Schwarz maps with symmetry*, arXiv:2601.02282v1 (5 January 2026;
quant-ph).

## Verified locator

DOI: 10.48550/arXiv.2601.02282.
Primary version: https://arxiv.org/abs/2601.02282v1 (the only arXiv version).
The TeX source of v1 supplies Eq. (`eq:abcd`) (the parameters a, b, c, d), the four
matrix-unit cases, the displayed Choi matrix, Lemma V.8 (`lem:eigChoi23`, PDF page 29) and
Remark V.2 (PDF page 32); the numbering is the printed one.

## Source statements

Eq. (`eq:abcd`): "$a \equiv \frac{1 - \lambda_{01} - \lambda_{10} + \lambda_{11}}{n_1 n_2} \, , \quad b \equiv \frac{\lambda_{01} - \lambda_{11}}{n_1} \, , \quad c \equiv \frac{\lambda_{10} - \lambda_{11}}{n_2}\, , \quad  d \equiv \lambda_{11}$".

Choi matrix: "$C_\Phi = a \mathbb I_{(n_1 n_2)^2} + b \sum_{k, l} (\mathbb I_{n_1} \otimes F_{kl})^{\otimes \ 2} + c \sum_{i, j} (E_{ij} \otimes \mathbb I_{n_2})^{\otimes 2} + d \sum_{i, j, k, l} (E_{ij} \otimes F_{kl})^{\otimes 2}$. We have no exact expression for its eigenvalues, but it is possible to compute their exact value for small dimension cases $(n_1, n_2) = (2, 2), (2, 3), (3, 2), (3, 3)$."

Lemma V.8: "For $n_1 = 2,3$; $n_2 = 2,3$, the eigenvalues of the Choi matrix $C_\Phi$ of a unital, hermiticity-preserving $U(n_1) \otimes U(n_2)$-equivariant map are given by: $\frac{1}{n_1 n_2} [1 + (n_2^2 - 1) \lambda_{01} + (n_1^2 - 1) \lambda_{10} + (n_1^2 - 1)(n_2^2 - 1) \lambda_{11}]$, with multiplicity 1. $\frac{1}{n_1 n_2} [1 + (n_2^2 - 1) \lambda_{01} - \lambda_{10} - (n_2^2 - 1) \lambda_{11}]$, with multiplicity $n_1^2 - 1$. $\frac{1}{n_1 n_2} [1 - \lambda_{01} + (n_1^2 - 1) \lambda_{10} - (n_1^2 - 1) \lambda_{11}]$, with multiplicity $n_2^2 - 1$. $\frac{1}{n_1 n_2} [1 - \lambda_{01} - \lambda_{10} + \lambda_{11}]$, with multiplicity $(n_1^2 - 1)(n_2^2 - 1)$."

Remark V.2: "Our results suggest, and thus we conjecture, that the eigenvalues of the Choi matrix $C_\Phi$ are given by Eqs. (\ref{eq:eigChoi23a})-(\ref{eq:eigChoi23d})."

## Scope

The equivariant maps are the combinations $\sum_{\alpha,\beta}\lambda_{\alpha\beta}P_\alpha\otimes P_\beta$ of the isotypic projections $P_0=D_i$ (trace to the scaled identity) and $P_1=\mathrm{id}-D_i$ of each factor, with $\lambda_{00}=1$ for unital maps and real $\lambda_{\alpha\beta}$ for Hermiticity-preserving ones. The paper uses the spectrum to describe complete positivity for $(n_1,n_2)=(2,2),(2,3)$ and to verify the PPT² property there.
