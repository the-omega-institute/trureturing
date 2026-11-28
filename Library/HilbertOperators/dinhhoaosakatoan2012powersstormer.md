---
bibkey: dinhhoaosakatoan2012powersstormer
authors: Dinh Trung Hoa; Hiroyuki Osaka; Ho Minh Toan
year: 2012
title: On generalized Powers-Størmer's Inequality
doi: 10.48550/arXiv.1204.6665
url: https://arxiv.org/html/1204.6665v1
claim: Matrix monotonicity of order 2n gives the generalized Powers–Størmer inequality for the canonical trace on n by n matrices, with the quotient t/f(t) set to zero at zero.
strata_touched:
  - D5/S3/Quantum/Lieb/FiniteOrderCompression
  - D5/S3/Quantum/Lieb/FiniteOrder/Ratio
  - D5/S3/Quantum/Lieb/FiniteOrder/SingularRatio
  - D5/S3/Quantum/Lieb/FiniteOrder/PowersStormer
license: citation-only
triage: anchor
---

# Finite-order generalized Powers–Størmer inequality

## Verified locator

DOI: https://doi.org/10.48550/arXiv.1204.6665

Primary version: https://arxiv.org/html/1204.6665v1

Metadata: https://arxiv.org/abs/1204.6665

## Scope and attribution

Lemma 2.1 gives contraction Jensen from monotonicity of order 2n.
Proposition 2.1 proves monotonicity of the ratio on positive definite
inputs using the contraction B^(-1/2) A^(1/2). Its stated premise makes
f strictly positive on the closed half-line. Proposition 2.2 and Corollary
2.1 address a zero extension. Theorem 2.1 states the trace inequality
for f positive on the open half-line, and explicitly defines g(0)=0.
Its proof uses the single common upper bound B+(A-B)^+=A+(A-B)^-.
No novelty is claimed for this inequality or this common-roof argument.

The Lean sources retain continuity of f on the closed half-line.
Positivity on the open half-line implies nonnegativity of f(0) by a
right-hand limit, and f(0)=0 is allowed. The endpoint proof first adds a
positive constant to f and uses a positive scalar matrix shift. It then
passes to the original quotient by pointwise convergence on the fixed
finite spectra. This argument does not assume continuity of the quotient
at zero. The trace is unnormalized, and all matrix functions are the
actual finite spectral functional calculus. The formal result includes
empty matrix carriers and singular noncommuting positive matrices.
