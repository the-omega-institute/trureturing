---
bibkey: rajaei2026generalized
authors: Reza Rajaei
year: 2026
title: "Generalized Fidelity and the Data Processing Inequality"
doi: null
url: https://arxiv.org/html/2609.09753v1
claim: "Generalized Bures--Wasserstein data processing fails in dimensions at least three; the unrestricted qubit case remains unresolved, with two sufficient conditions proved."
strata_touched:
  - D5/S3/Quantum/GeneralizedFidelity
license: citation-only
triage: anchor
---

# Generalized Fidelity and the Data Processing Inequality

The abstract of arXiv:2609.09753v1 states:

> In dimension two, although we do not settle the DPI in full generality,

The introduction defines

$$F_R(P,Q)=\operatorname{tr}\!\left(
\sqrt{\sqrt R P\sqrt R}\,R^{-1}\sqrt{\sqrt R Q\sqrt R}\right),
\qquad B_R(P,Q)=\operatorname{tr}(P+Q)-2\operatorname{Re}F_R(P,Q).$$

Every root is the positive semidefinite matrix root. The reference $R$ must
be positive definite; the introduction explicitly permits rank-deficient
$P,Q$. On density matrices, the trace term equals two. The residual qubit
question asks whether $B_{\Phi(R)}(\Phi(P),\Phi(Q))\le B_R(P,Q)$ for every
completely positive trace-preserving qubit channel with positive-definite
$\Phi(R)$.

The section *The Qubit Case* derives the nonzero positive semidefinite
two-dimensional root formula

$$\sqrt T=\frac{T+\sqrt{\det T}\,I}{\sqrt{\operatorname{tr}T+2\sqrt{\det T}}}.$$

It obtains an explicit real generalized-fidelity formula in terms of three
pairwise Uhlmann fidelities and proves two sufficient conditions for data
processing. These partial conditions do not settle the universal qubit
question. The paper's higher-dimensional counterexample is a different
settlement. Its necessary and sufficient condition for equality with Uhlmann
fidelity is also a separate statement.

Related sources are Afham and Ferrie, *Riemannian-geometric generalizations
of quantum fidelities and Bures-Wasserstein distance*, arXiv:2410.04937v2,
and Vuong, *Polar Fidelities,
Holevo Bases, and Unitary Factors of Generalized Fidelity*,
arXiv:2605.28885v1. The residual qubit universal inequality is narrower than
classification of all admissible reference bases.

## Verified locator

URL: https://arxiv.org/html/2609.09753v1 (version 1).
The abstract explicitly retains the unrestricted dimension-two DPI
question. The introduction defines the ordered matrix-root fidelity and
the generalized Bures--Wasserstein quantity and permits rank-deficient
input states. *The Qubit Case* gives the two-dimensional PSD-root formula
and the two sufficient qubit DPI conditions.
