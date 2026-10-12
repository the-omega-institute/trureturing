---
bibkey: ricozyczkowski2024measurements
authors: Albert Rico; Karol Życzkowski
year: 2024
title: "Discrete dynamics in the set of quantum measurements"
doi: 10.1088/1751-8121/ad7dc2
url: https://arxiv.org/abs/2308.05835v2
claim: "Conjecture 1 asserts that blockwise bistochastic dynamics allow an input ordering whose every centered prefix has 2-norm at least that of any prescribed output ordering."
strata_touched:
  - D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation
license: citation-only
triage: anchor
---

# Discrete dynamics in the set of quantum measurements

A. Rico and K. Życzkowski, J. Phys. A: Math. Theor. 57 (2024) 435302;
arXiv:2308.05835v2.

## Verified locator

DOI: 10.1088/1751-8121/ad7dc2

DOI URL: https://doi.org/10.1088/1751-8121/ad7dc2

Source: https://arxiv.org/abs/2308.05835v2

Definition 1, p. 4; Definition 3, Eq. (19), p. 8; Definition 5, p. 12;
Appendix C.1, Conjecture 1, p. 28; Appendix C.2, pp. 29–30 (the n = 2 case).
Page numbers refer to the arXiv v2 PDF.

## Source definitions

Definition 1 (equations rendered inline):

> A blockwise probability vector is a column vector P = (P_1, …, P_n)^T,
> with n components P_j being Hermitian, positive semidefinite matrices of order d,
> P_j ≥ 0, satisfying the identity resolution Σ_{j=1}^n P_j = 1_d.

Definition 3, Eq. (19) (equation rendered inline):

> Let A and B be two matrices A = (A_ij) ∈ C^{dn} × C^{dn′} and
> B = (B_ij) ∈ C^{dn′} × C^{dn′′} composed of n × n′ and n′ × n′′
> positive semidefinite blocks of size d, A_ij, B_ij ∈ C^d × C^d.
> We define the blockwise product,
> (A ∗ B)_ik = Σ_j √B_jk A_ij √B_jk ∈ C^{dn} × C^{dn′′}.

Definition 5 (equation rendered inline):

> Let B be a square matrix of size dn × dn composed of n² blocks B_ij
> of size d × d each. We call B blockwise bistochastic if
> (i) its entries B_ij are positive semidefinite matrices of size d ≥ 2
> (ii) its blockwise columns and rows sum to identity, Σ_i B_ij = Σ_j B_ij = 1_d.

## Conjecture 1

Appendix C.1, p. 28, verbatim:

> Let P ∈ Δ_{n,d} and Q ∈ Δ_{n,d} be blockwise probability vectors. If there exists a blockwise bistochastsic matrix B ∈ B_{n,d} such that Q = B ∗ P, then for any ordering of {Q_i} there exists an ordering of {P_i} such that ‖Σ_{i=1}^{k}(P_i − 1/n)‖₂ ≥ ‖Σ_{i=1}^{k}(Q_i − 1/n)‖₂ for all 1 ≤ k ≤ n, where ‖A‖₂ = √tr[A†A] is the 2-norm.

Here 1/n denotes the scalar multiple of the d-dimensional identity. The
2-norm is the Hilbert–Schmidt norm. Appendix C.2 proves the two-outcome case.
Theorems 2 and 3 concern linear monotones for sortable measurements; the
conjecture asks for a nonlinear monotone outside that sortable set.
