---
bibkey: vanherstraeten2024majorization
authors: Zacharie Van Herstraeten; Nicolas J. Cerf; Saikat Guha; Christos N. Gagatsos
year: 2024
title: "Majorization theoretical approach to entanglement enhancement via local filtration"
doi: 10.1103/PhysRevA.110.042430
url: https://arxiv.org/abs/2312.02066v2
claim: "With N_kk = sum_n lambda^n C(n+k,k)^2 and coefficients c_n^(kk) defined by C(n+k+1,k)^2 = sum_{i=0}^{n+1} c_{n-i}^(kk) (i+1)^2, c_{-1}^(kk) = 1, the authors conjecture that all c_n^(kk) are non-negative for every k >= 2, i.e. that the matrix D with q^(kk) = D q^(11) is column stochastic, implying the majorization relation sigma^(k,k) < sigma^(1,1) (proved for k = 2, ..., 8, with closed forms printed for k = 2, 3, 4)."
strata_touched:
  - D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients
license: citation-only
triage: anchor
---

# Majorization theoretical approach to entanglement enhancement via local filtration

Z. Van Herstraeten, N. J. Cerf, S. Guha and C. N. Gagatsos, arXiv:2312.02066
(v1 2023-12-04, v2 2026-01-21); Phys. Rev. A 110 (2024) 042430. Subject:
quant-ph.

The paper compares two-mode squeezed vacuum states after local photon
addition and subtraction through majorization of their Schmidt coefficients.
For `k` photons added to each mode the Schmidt coefficients are
`q_n^{(kk)} = λⁿ C(n+k,k)² / N_kk` with `N_kk = Σ_n λⁿ C(n+k,k)²`. The
appendix "Majorization relations among different photon-added TMSV" writes
`q^{(kk)} = D q^{(11)}` with a lower-triangular Toeplitz matrix `D` whose
entries are `λN_11/N_kk · c_m^{(kk)} λ^m`, where

> \binom{n+k+1}{k}^2 = \sum_{i=0}^{n+1} c_{n-i}^{(kk)} (i+1)^2

and `c_{-1}^{(kk)} = 1`. The columns of `D` sum to `1`. The paper proves `c_n^{(kk)} ≥ 0` for
`k = 2, …, 8`, printing the closed forms for `k = 2, 3, 4`, and then states:

> At this point, we conjecture the non-negativity of Eq.
> \eqref{eqapp:Coeffcients}, \textit{i.e.}, we conjecture that the matrix
> $\mathbf{D}$ of Eq. \eqref{eqapp:Dvector} is column stochastic for all
> $k\geq 2$, implying the majorization relation $\hat{\sigma}^{k,k} \prec
> \hat{\sigma}^{1,1}$.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.110.042430 (the journal text was not
  read).
- URL: https://arxiv.org/abs/2312.02066v2 (source `main.tex` retrieved
  2026-10-01): the appendix "Majorization relations among different
  photon-added TMSV" (the definition of `c_n^{(kk)}`, the closed forms for
  `k = 2, 3, 4` and the conjecture) and the main-text paragraph stating that
  the cases `k = 2, …, 8` were proved.
