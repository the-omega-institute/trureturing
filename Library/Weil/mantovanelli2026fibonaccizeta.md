---
bibkey: mantovanelli2026fibonaccizeta
authors: Marco Mantovanelli
year: 2026
title: The Right Edge of the Zero Set of the Fibonacci Zeta Function
doi: null
url: https://arxiv.org/abs/2609.04993v1
claim: The preprint determines the right edge of the zero set of the Fibonacci zeta function and constructs an entire completion; the result concerns a Fibonacci Dirichlet series and does not transfer to the Riemann zeta function or Robin's inequality.
strata_touched: []
license: citation-only
triage: anchor
---

# The right edge of the Fibonacci zeta zero set

The source is [arXiv:2609.04993v1](https://arxiv.org/pdf/2609.04993v1), submitted 4 September 2026. The statements below are attributed to that version; its proof and numerical constants were not independently audited here, and no Lean verification is claimed.

It studies

$$
Z_F(s)=\sum_{n\ge1}F_n^{-s}
$$

and determines the right edge of the closure of the real parts of its zeros in the half-plane of absolute convergence. If $\sigma_F$ is the unique solution of

$$
Z_F(\sigma_F)=4+2\,144^{-\sigma_F},
$$

the paper reports

$$
\sigma_F=0.743163398726901648\ldots,
$$

with no zeros of $Z_F$ for $\operatorname{Re}s\ge\sigma_F$ and zeros approaching every admissible vertical line to the left. It also gives finite-partial-sum edges, a Lucas-zeta core theorem, and an entire completion of order $2$.

## Boundary of the RH interface

The Fibonacci growth in the exponents makes this source relevant to FIB recursive geometry, but $Z_F$ has not supplied the Euler product, von Mangoldt coefficients, or explicit formula for $\zeta(s)$. Its zero-free edge is therefore a theorem about a different almost-periodic Dirichlet series. No implication to the Riemann hypothesis, Robin's $\sigma(n)/n$ bound, or the signed $\Phi$ tail follows from the edge value alone.

The usable interface is diagnostic: a FIB-generated zeta-like object can have a sharp zero boundary without sharing the arithmetic test set of $\zeta$. Any proposed FIB spectral proof of RH must exhibit an actual coefficient-preserving map to the Riemann zeta explicit formula.
