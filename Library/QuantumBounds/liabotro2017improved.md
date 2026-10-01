---
bibkey: liabotro2017improved
authors: Ola Liabøtrø
year: 2017
title: "Improved Classical and Quantum Random Access Codes"
doi: 10.1103/PhysRevA.95.052315
url: https://arxiv.org/abs/1607.02667v2
claim: "For maximal (4^m - 1, m, p) quantum random access codes with the paper's projective measurements, the worst-case success probability is governed by the most negative eigenvalue of the signed Pauli sums Sigma(beta) = sum_{k=1}^{4^m-1} (-1)^{beta(k)} sigma_{c_1(k)} x ... x sigma_{c_m(k)}; the paper checks m = 1, 2 exhaustively and conjectures ||Sigma(beta)|| <= (sqrt(3) + 1)^m - 1 for all m and all beta (Eq. (78))."
strata_touched:
  - D5/S3/Quantum/Information/SignedPauliSumNormRefutation
license: citation-only
triage: anchor
---

# Improved Classical and Quantum Random Access Codes

O. Liabøtrø, arXiv:1607.02667 (v1 2016-07, v2 2016-11-28, the latest);
Phys. Rev. A 95, 052315 (2017). Subject: quant-ph.

The paper constructs classical and quantum random access codes encoding `n`
`d`-levels into `m` (qu)-`d`-levels and optimizes their success probabilities.
For maximal `(4^m − 1, m, p)` qubit codes built from the Pauli measurement
operators, the worst-case success probability is expressed through `−λ`, the
most negative eigenvalue of the matrices

`Σ(β) = Σ_{k=1}^{4^m−1} (−1)^{β(k)} ⊗_{i=1}^{m} σ_{c_i(k)}`,

where `σ_0 = I`, `σ_1, σ_2, σ_3` are the Pauli matrices, `c_i(k)` is the `i`-th
base-4 digit of `k`, and `β` is any function `{1, …, 4^m − 1} → {0, 1}`. The
matrix `I − (I + σ_x + σ_y + σ_z)^{⊗m}` gives the bound
`p ≤ (1 + 1/((1+√3)^m − 1))/2`, and the paper states:

> We have checked numerically that no $\Sigma(\beta)$ has an eigenvalue less
> than $1-(1+\sqrt(3))^m$ for $m=1,2$. This means that we can obtain equality in
> the bound in these cases. We conjecture that this is the case for all $m$,
> i.e.: $||\sum_{k=1}^{4^m-1}(-1)^{\beta(k)}\bigotimes_{i=1}^m\sigma_{c_i(k)}||\leq (\sqrt{3}+1)^m-1$

Random searches up to `m = 6` found no counterexample (the paper's table of
random eigenvalues).

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.95.052315 (the journal text was not
  read).
- URL: https://arxiv.org/abs/1607.02667v2 (source retrieved 2026-09-30):
  `paper_v2.tex`, the Pauli word notation (l. 266–268), the matrices `Σ(β)`
  (l. 619–621), the conjecture (l. 633–638, Eq. (78) of the PDF) and the random
  searches (l. 640 and the table `randomeigenvalues`).
