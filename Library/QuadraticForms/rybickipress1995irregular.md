---
bibkey: rybickipress1995irregular
authors: George B. Rybicki; William H. Press
year: 1995
title: Class of Fast Methods for Processing Irregularly Sampled or Otherwise Inhomogeneous One-Dimensional Data
doi: 10.1103/PhysRevLett.74.1060
url: https://arxiv.org/abs/comp-gas/9405004v1
claim: The irregularly sampled exponential correlation matrix has a tridiagonal inverse; its coefficients expand to the unequal-gap innovation quadratic form.
strata_touched:
  - D5/S3/Quantum/Entanglement/ExponentialKernel/InverseQuadraticForm
license: citation-only
triage: anchor
---

# The inverse of an irregular exponential correlation matrix

G. B. Rybicki and W. H. Press, *Class of Fast Methods for Processing
Irregularly Sampled or Otherwise Inhomogeneous One-Dimensional Data*,
Physical Review Letters **74**, 1060-1063 (1995).

## Verified locator

DOI: https://doi.org/10.1103/PhysRevLett.74.1060

Preprint: https://arxiv.org/abs/comp-gas/9405004v1

The displayed formulas on PDF pages 2-3 of the preprint were inspected.
Equation (1) defines the symmetric correlation matrix by the exponential of
minus the absolute integrated decorrelation rate. Equations (2)-(4) give its
tridiagonal inverse and the adjacent parameters

\[
r_i=\exp\!\left(-\int_{t_i}^{t_{i+1}}w(t)\,dt\right),
\qquad e_i=(r_i^{-1}-r_i)^{-1}.
\]

The journal title, authors, year, volume, page range and DOI agree with the
Crossref record for this DOI. No earliest-appearance claim is made.

## Parameter correspondence and quadratic form

Set the decorrelation rate to the constant \(w=1/2\), take
\(t_i=\ell_i\) with \(\ell_1<\cdots<\ell_k\), and set the population
variance to one. Then the source correlation matrix is
\(K_{ij}=\exp(-|\ell_i-\ell_j|/2)\), its adjacent parameter is
\(r_i=\kappa_i\), and
\(e_i=\kappa_i/(1-\kappa_i^2)\).

For at least two sites, the tridiagonal coefficients give

\[
T_{11}=\frac1{1-\kappa_1^2},\qquad
T_{kk}=\frac1{1-\kappa_{k-1}^2},\qquad
T_{i,i+1}=T_{i+1,i}=-\frac{\kappa_i}{1-\kappa_i^2},
\]

and, at an interior index,

\[
T_{ii}=\frac1{1-\kappa_{i-1}^2}
       +\frac{\kappa_i^2}{1-\kappa_i^2}.
\]

The off-diagonal index ranges printed in equation (2) exclude the boundary
adjacent entries. The coefficients above apply to every adjacent pair; this
full range follows from the explicit innovation factorization used in the
Lean proof. The printed index inequalities are not adopted as the scope of
the inverse identity.

Expanding the squares on the right below gives precisely these diagonal and
off-diagonal coefficients:

\[
x^T K^{-1}x=x_1^2+
  \sum_{i=1}^{k-1}\frac{(x_{i+1}-\kappa_i x_i)^2}{1-\kappa_i^2}.
\]

The one-site matrix is \([1]\); its quadratic form is \(x_1^2\), with an
empty innovation sum. This endpoint follows directly from that matrix.

The Lean proof constructs the bidiagonal innovation matrix and identifies the
actual nonsingular matrix inverse. It uses only the adjacent strict
inequalities within the finite site family and permits arbitrary real
vectors. The known covariance identity supplies no physical channel
optimality or realization claim.
