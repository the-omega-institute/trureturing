---
bibkey: he2025operatorconvexity
authors: Kerry He, James Saunderson, and Hamza Fawzi
year: 2025
title: Operator convexity along lines, self-concordance, and sandwiched Rényi entropies
doi: 10.1007/s10107-025-02314-0
url: https://arxiv.org/abs/2502.05627v1
claim: Conjecture 6.2 in arXiv v1, renumbered Conjecture 1 in the journal article, proposes the sharp compatibility parameter (2 alpha - 1)/3 for the sandwiched trace function in every finite dimension.
strata_touched:
  - D5/S3/Quantum/Matrix/HsfCubicRadial
  - D5/S3/Quantum/Matrix/RpowPencilTaylor
  - D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate
  - D5/S3/Quantum/Matrix/HsfBalancedCfcBridge
license: citation-only
triage: anchor
---

# Sandwiched trace compatibility

For positive definite complex Hermitian matrices, the source considers

\[
\Psi_\alpha(X,Y)
=\operatorname{Tr}\!\left[
  \left(Y^{(1-\alpha)/(2\alpha)}X
        Y^{(1-\alpha)/(2\alpha)}\right)^\alpha
\right].
\]

The conjecture covers every positive integer dimension and every
\(\alpha\ge2\). In directional derivative form, for Hermitian directions
with \(X\pm H,Y\pm K\succeq0\), its proposed sharp estimate is
\(|g'''(0)|\le(2\alpha-1)g''(0)\), where
\(g(t)=\Psi_\alpha(X+tH,Y+tK)\).
The journal article's Proposition 3 proves the scalar result and its
sharpness; Conjecture 1 asks for the matrix extension.

The repository's `HsfCubicRadial` proves the normalized polynomial-trace
estimate at \(\alpha=3\): for Hermitian \(A,B\) with
\(A\pm B\succeq0\), the actual function
\(f(t)=\operatorname{Re}\operatorname{Tr}[(A+tB)^3]/(1+kt)^2\)
satisfies \(f''(0)\ge0\) and
\(|f'''(0)|\le(1+4|k|)f''(0)\). Over \(|k|\le1\), the least
uniform constant is 5. Its proof is repository-derived and allows
noncommuting matrices. Its physical radial application takes
\(K=kY\), \(S=Y^{-1/3}\), \(A=SXS\), and \(B=SHS\).
For positive definite \(X,Y\) and Hermitian \(H\) with
\(X\pm H\succeq0\), positive-scalar CFC scaling identifies the original
trace function with \(f\) near zero. Thus its actual second and third
derivatives satisfy the same bound, including singular endpoints.
General second-variable directions and other exponents are outside
this application; it does not resolve the conjecture.

The current formal library extends this record with a separate, explicitly
scoped two-level supplier. `D5/S3/Quantum/Matrix/RpowPencilTaylor` proves
for an arbitrary finite-dimensional positive definite complex Hermitian center
`Y` and Hermitian direction `K` that the actual CFC cube-root pencil is smooth
near zero (`contDiffAt_cubeRoot`), that its first three
factorial-normalized jets satisfy the ordered noncommutative cubic recurrences
(`cubeRoot_jet_recurrences`), and that the actual two-thirds power is smooth
(`contDiffAt_twoThirds`) with the corresponding ordered jet formula
(`normalized_twoThirds_jet`). Its fixed spectral-coordinate interface
(`cubeRoot_jet_spectral`) has strictly positive entrywise divisors, including
repeated eigenvalues; it does not assume commutation, a spectral floor, or a
derivative premise.

`D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate` supplies the finite
weighted PSD Gram certificate for the displayed two-level frame. The two
diagonal blocks may have arbitrary finite multiplicities and the off-diagonal
block is an arbitrary rectangular complex matrix, subject to positivity of the
full block direction. The diagonal blocks are therefore consequences of this
single full-block PSD hypothesis, not independent arbitrary-PSD inputs.
Singular directions and `r=1` are included, and the certificate keeps all
matrix multiplication orders. Its `supplier_of_cubic_recurrence` theorem is
the repository's balanced cubic algebraic certificate, not a claim about an
arbitrary spectrum.

`D5/S3/Quantum/Matrix/HsfBalancedCfcBridge.actual_twoLevel_supplier` consumes
the actual CFC jets and gives the stated weighted inequality in that supplied
two-level frame. Its
`D5/S3/Quantum/Matrix/HsfBalancedCfcBridge.transported_twoLevel_supplier`
version permits only the supplied finite reindexing, unitary conjugation, and
common positive scaling of the center and direction. It does not extract a
frame from a bare eigenvalue-count premise and does not provide nonunitary
congruence or arbitrary PSD diagonal blocks outside the displayed hypothesis.
There is no formal three-level or arbitrary-spectrum theorem here, and this
library update does not claim the full all-`alpha` HSF conjecture, a novelty
result, or an official open-problem resolution. The primary HSF source and
the original radial `alpha=3` exposition above remain the citation anchor.

## Verified locators

- arXiv:2502.05627v1, Conjecture 6.2 and the preceding scalar discussion.
- DOI 10.1007/s10107-025-02314-0, Proposition 3 and Conjecture 1.

These sources identify the target and scalar predecessor. This note does
not establish bibliographic priority or exclude a later resolution.
