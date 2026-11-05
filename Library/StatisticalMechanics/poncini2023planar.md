---
bibkey: poncini2023planar
authors: Xavier Poncini and Jørgen Rasmussen
year: 2023
title: Integrability of planar-algebraic models
doi: 10.1088/1742-5468/acdce7
url: https://arxiv.org/abs/2206.14462v2
claim: "Conjecture C.12 gives the eight-vertex transfer matrix as a central factorial polynomial expansion of its principal Hamiltonian."
strata_touched:
  - D5/S1/Recurrence/CentralFactorialTransferExpansion
  - D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1088/1742-5468/acdce7

Source: https://arxiv.org/abs/2206.14462v2

## Source statement

Page 47, Conjecture C.12:

> For every n ∈ ℕ and all u ∈ F, we have Ť_n(u) = 2 Σ_{k=0}^{n−1} (1 + u²)^{n−k} (2u)^k Σ_{j=0}^{⌊k/2⌋} [n − k − 2 + 2j over 2j]!! (−1)^j m_{k−2j}(h_n)/(k − 2j)!

> We have verified Conjecture C.12 for n = 1, . . . , 180.

Here F is algebraically closed of characteristic zero and n ≥ 1. Equations
(C.9)–(C.15) define the two-site coefficients, the ordered double row and its
auxiliary partial trace. Page 45, equation (C.40) reads “h_n = Σ_{i=1}^{n−1} σ^x_{n,i}
σ^x_{n,i+1}”. Equation (C.44) reads “m_j(x) := Π_{k=0}^{j−1}
[x − (j − 1 − 2k)], j ∈ ℕ.” Equation (C.65) defines the coefficient as
“n_1!!/(n_2!!(n_1 − n_2)!!)”. The integer double factorial uses (−1)!! = 0!! = 1.

The tensor basis is Fin n → Fin 2, with zero-based coordinates. The two-site
matrix entry at row x and column y is the coefficient R^{x(a),x(b)}_{y(a),y(b)}
when the other coordinates agree. The auxiliary partial trace sums the two
entries obtained by appending the same bit to x and y.

## Scope

Proposition C.3 supplies the adjacent-flip product form; Propositions C.4 and
C.6 describe its common eigenvectors and eigenvalues. The coefficient identity
and the universal matrix conclusion are proved in the corresponding Lean
modules. Preregistration: https://github.com/the-omega-institute/trureturing/issues/19637.
Completeness of the prior-art search is ASSUMED-UNVERIFIED; no priority claim
is made. The inaccessible thesis and complete citation coverage remain unverified.
