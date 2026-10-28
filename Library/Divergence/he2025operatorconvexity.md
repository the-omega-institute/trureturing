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
noncommuting matrices. An equality with the physical CFC-power expression
is not formalized there. General second-variable directions and other
exponents are outside that module; it does not resolve the conjecture.

## Verified locators

- arXiv:2502.05627v1, Conjecture 6.2 and the preceding scalar discussion.
- DOI 10.1007/s10107-025-02314-0, Proposition 3 and Conjecture 1.

These sources identify the target and scalar predecessor. This note does
not establish bibliographic priority or exclude a later resolution.
