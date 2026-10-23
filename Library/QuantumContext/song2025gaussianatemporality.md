---
bibkey: song2025gaussianatemporality
authors: Minjeong Song; Jayne Thompson; Matthew S. Winnel; Biveen Shajilal; Timothy C. Ralph; Syed M. Assad; Mile Gu
year: 2025
title: "Gaussian Atemporality: When Gaussian Quantum Correlations Imply Common Cause"
doi: 10.48550/arXiv.2508.11804
url: https://arxiv.org/abs/2508.11804v2
claim: "Section III.D states: From Fig. 3, Gaussian-atemporality appears to imply entanglement."
strata_touched:
  - D5/S3/Estimation/GaussianAtemporalityEntanglement
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2508.11804

Source: https://arxiv.org/abs/2508.11804v2

The PDF of v2, Section III.D (the fourth subsection of Section III), p. 6:

> From Fig. 3, Gaussian-atemporality appears to imply entanglement. The converse, on the other hand is not generally true.

Definition 1, p. 3:

> Let Alice and Bob each have access to a qumode with standard basis $(\widehat{q}_{A},\widehat{p}_{A})$ and $(\widehat{q}_{B},\widehat{p}_{B})$, with locally diagonal covariance matrices $\mathbf{V}_{A}$ and $\mathbf{V}_{B}$.

Equation (2) is the block matrix $\mathbf{V}_{AB}=\begin{pmatrix}\mathbf{V}_{A}&C\\C^{T}&\mathbf{V}_{B}\end{pmatrix}$.
The quadrature order is $(q_A,p_A,q_B,p_B)$, with $\hbar=2$.
Equation (7), p. 4, gives $\mathbf{T}=C^{T}\mathbf{V}_{A}^{-1}$ and
$\mathbf{N}=\mathbf{V}_{B}-C^{T}\mathbf{V}_{A}^{-1}C$.
Equation (8), p. 4, gives $\mathbf{X}(\mathbf{T},\mathbf{N})\equiv\mathbf{N}+i\Omega-i\mathbf{T}\Omega\mathbf{T}^{T}$.

Section III.B, p. 4:

> We then say that $\mathbf{V}_{AB}$ is Gaussian atemporal if it is Gaussian-atemporal in both temporal direction.

The two-mode covariance formulation uses failure of the partially transposed
uncertainty inequality as its entanglement predicate. The analytic equivalence
with Hilbert-space separability is the Gaussian PPT criterion used by the source;
it is not independently formalized in the covariance theorem.

The formal implication uses positivity under matrix congruence. It also proves,
inside the settling proof, that PPT implies temporal compatibility in both
directions without requiring diagonal local blocks. It does not settle a
quantitative threshold for entanglement forcing atemporality.
