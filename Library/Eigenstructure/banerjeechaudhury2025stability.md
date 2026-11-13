---
bibkey: banerjeechaudhury2025stability
authors: Debraj Banerjee; Kunal N. Chaudhury
year: 2025
title: "On the Schur Stability of Some Image Reconstruction Operators"
doi: null
url: https://arxiv.org/abs/2509.06715v1
claim: "Conjecture 1.1 proposes simultaneous Schur stability of W(I-tB) and I-W+(I+tB)^(-1)(2W-I) for every 0<t<2/rho(B), under primitivity, stochasticity, positive semidefiniteness, Be<=rho(B)e and pi^T Be>0."
strata_touched:
  - D5/S3/Quantum/Matrix/BanerjeeChaudhuryStabilityRefutation
license: CC-BY-4.0
triage: anchor
---

# On the Schur Stability of Some Image Reconstruction Operators

Debraj Banerjee and Kunal N. Chaudhury, arXiv:2509.06715v1.
The [original source](https://arxiv.org/src/2509.06715v1) is licensed
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
The SHA-256 of `manuscript.tex` is
`2a828b151c14f8bff40243c0a56cc6a9d3b4efce27e4258215db2940ad9baf4b`.

The source fixes a positive dimension, real matrices W and nonzero B,
the all-ones vector e, and the spectral radius as the largest modulus
of a complex eigenvalue. Schur stability means that this radius is less
than one (`manuscript.tex`, lines 117–138). Its operators are

$$P(t)=W(I-tB),\qquad R(t)=I-W+(I+tB)^{-1}(2W-I).$$

The inverse is assumed to exist. Stochastic means entrywise nonnegative
with We=e. Primitive means that one positive power has every entry
strictly positive. The left Perron vector is positive and normalized
by pi transposed times e equal to one. Line 300 fixes the nonsymmetric
stochastic setting for the subsequent conjecture.

Conjecture 1.1 (`manuscript.tex`, lines 324–328) states:

> Let $W$ be primitive and stochastic, and let $B$ be positive semidefinite with $Be \leqslant \varrho(B) e$ and $\pi^\top Be > 0$, where $\pi$ is the left Perron eigenvector of $W$. Then $P(t)$ and $R(t)$ are stable for all $0 < t < 2/\varrho (B)$.

The repository refutes this full conjunction through P at dimension four.
It does not assert instability of R, solve the broader classification
in Problem 1.1, or provide new spectral theory. The separate positive
results under their stated stronger hypotheses are outside this refutation.
