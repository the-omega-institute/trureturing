---
bibkey: "janson2021mdependent"
authors: "Svante Janson"
year: 2021
title: "A central limit theorem for m-dependent variables"
doi: "10.48550/arXiv.2108.12263"
url: "https://arxiv.org/abs/2108.12263v1"
claim: "A centered m-dependent triangular array satisfies a central limit theorem under a Lindeberg condition; for fixed dependence range, a vanishing Lyapunov ratio with any moment order greater than two suffices."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# A central limit theorem for m-dependent variables

The inspected source is arXiv:2108.12263v1 (27 August 2021), 12 pages.
Theorem 1.1, page 1, states the central limit theorem for a fixed dependence
range and centered, square-integrable triangular arrays with positive row-sum
variance and the usual Lindeberg condition. Theorem 4.1, page 7, gives the
Lyapunov form: for moment order `p > 2`, dependence range `m_N`, and row-sum
standard deviation `sigma_N`, it suffices that
`m_N^(p-1) sum_i E|X_Ni|^p / sigma_N^p -> 0`.
For independent summands within each row, one may take dependence range
one, as explained in Remark 1.5; range two applies to the path-edge arrays here.

This central limit theorem is `literature-attested`. The parity-kernel
application must separately establish the two-step reset under the normalized
double likelihood tilt, compare its uniform and stationary initial laws, and
bound its means, covariance matrix and absolute third moments uniformly over
all amplitudes in `(0,1)`. Those model-specific calculations and the resulting
critical-window risk and recovery curves are `repo-derived` deductions. The
source itself does not state those statistical experiments or curves.
