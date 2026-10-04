---
bibkey: leinster2011magnitude
authors: Tom Leinster
year: 2011
title: The magnitude of metric spaces
doi: 10.48550/arXiv.1012.5857
url: https://arxiv.org/abs/1012.5857v3
claim: A finite subset of the real line has explicit positive similarity-matrix weights and magnitude equal to one plus a sum of adjacent hyperbolic tangents.
strata_touched:
  - D5/S3/Quantum/Entanglement/ExponentialSectorKernel
license: citation-only
triage: anchor
---

# The Magnitude of Metric Spaces

Corollary 2.3.4 of arXiv:1012.5857v3 treats a finite subset
`A = {a_0 < ... < a_n}` of the real line. Its similarity matrix has
entries `exp(-abs(a_i-a_j))`. With adjacent distances
`d_i = a_i-a_(i-1)`, the magnitude is
`1 + sum_i tanh(d_i/2)`. The weight at an interior point is half
the sum of the two neighboring hyperbolic tangents. At an endpoint,
the missing neighbor contributes one. The singleton therefore has
weight and magnitude one.

Proposition 2.4.3 gives the variational formula for a positive definite
finite metric space: its magnitude is the supremum of the squared sum
of a nonzero real vector divided by its similarity-matrix quadratic
energy. Equality holds exactly at nonzero scalar multiples of the
unique weighting. A positive weighting, normalized to sum one,
therefore attains the reciprocal magnitude as the simplex energy
minimum.

## Correspondence

For ordered loss values `ell_i`, set `a_i = ell_i/2`. The similarity
matrix becomes `exp(-abs(ell_i-ell_j)/2)`, and the magnitude becomes
`Z = 1 + sum_i tanh((ell_(i+1)-ell_i)/4)`.
`ExponentialSectorKernel.result` constructs the corresponding
equilibrium weights recursively and proves the exact minimum `1/Z`.
Its proof uses a direct endpoint completion of squares and the row
identity `Kv=1`. The formal statement also permits coincident indexed
sites and proves nonnegative weights without asserting invertibility
of the repeated-site matrix. The distinct-point magnitude result does
not itself establish that repeated-site statement.

The metric-space formula supplies the mathematical attribution for
the kernel minimum. It does not assert any quantum-channel distance,
independent-local-operation optimum, integer-rank conversion criterion,
or physical interpretation of a loss operator.

## Verified Locators

- Version: arXiv:1012.5857v3, revised 22 January 2011.
- Corollary 2.3.4: https://arxiv.org/html/1012.5857v3#S2.SS3.Thmthm4
- Proposition 2.4.3: https://arxiv.org/html/1012.5857v3#S2.SS4.Thmthm3
- The arXiv abstract and HTML returned HTTP 200 on 27 September 2026;
  both displayed statements were checked against the original text.
