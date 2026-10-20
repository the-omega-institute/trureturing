---
bibkey: chirvasitucusick2024quadraticrotation
authors: A. Chirvasitu; T. W. Cusick
year: 2024
title: 'Quadratic rotation symmetric Boolean functions'
doi: 10.1016/j.dam.2023.10.010
url: https://arxiv.org/abs/2304.12734v1
claim: Section 6 defines the binomial rules matrices R(i,j) and Conjecture 6.1 proposes their scaled-root-of-unity spectrum and order 2 lcm(4, i-j, i+j).
strata_touched:
  - D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder
license: citation-only
triage: anchor
---

# Quadratic rotation symmetric Boolean functions

A. Chirvasitu and T. W. Cusick, *Quadratic rotation symmetric Boolean functions*,
Discrete Applied Mathematics 343 (2024), 91–105.

## Verified locator

DOI: https://doi.org/10.1016/j.dam.2023.10.010

Source: https://arxiv.org/abs/2304.12734v1

## Source statement

Conjecture 6.1, page 19:

> For i > j ≥ 1 the eigenvalues of the matrix R(i, j) of (6-3) are all √2-scaled roots of unity.
> Moreover, the multiplicative order of R(i,j)/√2 is precisely 2 · lcm(4, i − j, i + j).

Section 6, page 18, defines $H_0=\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ and
$H_1=\begin{pmatrix}1&1\\-1&1\end{pmatrix}$. On page 19:

> by πₖ(M) (or πₖM) the matrix obtained by appending k all-0 columns after each column of M (‘π’ is meant to stand for ‘pad’);

> and by ρₖ(M) (or ρₖM) the matrix obtained by rotation all rows of M simultaneously rightward k times.

> Specifically, the rows in (6-2) alternate in whether or not an H₁ is substituted in batches of 2ʲ⁻¹:

Equation (6-3) starts with $H_0$ and stacks the successive rotated padded blocks.
The source states: “Again, this is a 2ⁱ × 2ⁱ matrix.” Zero-based block and row
indices correspond by $(k,c)\mapsto c+2k$.

The formal refutation concerns the order conjunct at $(8,4)$. It does not
establish the exact order 48 or decide the universal eigenvalue conjunct.
Completeness of the search for a prior published settlement is ASSUMED-UNVERIFIED.

## Experiment entry

The independent checker is in
[trureturing-experiments](https://github.com/the-omega-institute/trureturing-experiments/blob/f6f05757e065d45c0f14bce4085f46b713d78896/docs/reports/chirvasitu-cusick-2023-rules-matrix-order/check.py),
commit `f6f05757e065d45c0f14bce4085f46b713d78896`, SHA-256
`f364b6795d229f1352f9ff59f297ef56fe0d08f4b7dbf2ef2ae3933f85e57e78`.
Running `OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 python3 docs/reports/chirvasitu-cusick-2023-rules-matrix-order/check.py`
in that repository exits 0 with `RESULT PASS`. The matrix powers at $(8,4)$ use
integer arithmetic; the broader order scan uses floating arithmetic.
