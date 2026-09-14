---
bibkey: higham2006eigenstate
authors: Nicholas J. Higham
year: 2006
title: Functions of Matrices
doi: null
url: https://eprints.maths.manchester.ac.uk/310/
claim: Matrix Taylor series act scalarly on an eigenline, and the standard pure-state trace formulas give a positive normalized density matrix and zero energy variance.
strata_touched:
  - D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity
license: citation-only
triage: anchor
---

# Matrix series and pure eigenstates

## Verified locator

The exact upstream locator is:
https://eprints.maths.manchester.ac.uk/310/

The record identifies Higham's 2006 chapter in the Handbook of Linear
Algebra. Its PDF, https://eprints.maths.manchester.ac.uk/310/1/fm_final.pdf,
was retrieved: section 1, fact 10 gives the matrix Taylor-series formula;
section 3 defines the matrix exponential by `sum_{k>=0} A^k/k!`.

The companion source is John Preskill, Ph219/CS219, Chapter 2,
Foundations I: States and Ensembles:
https://www.preskill.caltech.edu/ph219/chap2_15.pdf
The retrieved text gives `mean(A)=<psi|A|psi>` in (2.9), the trace expectation
in (2.62), positivity and trace one on page 20, and the pure density matrix
`rho=|psi><psi|` on that page.

## Shared source chain and declaration bridges

- `exp_mulVec_of_eigenvector`: if `Av=mu v`, induction gives
  `A^k v=mu^k v`. Apply the continuous linear map `B -> Bv` to the
  convergent matrix exponential series, then use uniqueness of the sum:
  `exp(A)v = sum_k mu^k v/k! = exp(mu)v`. Exponential has infinite radius
  of convergence. This argument applies to every finite complex matrix,
  including n=0, and permits v=0. It requires neither Hermitian A nor
  diagonalizability nor a nonzero vector; a theorem imposing those stronger
  conditions is not used as a substitute. The local proof implements the
  bridge with `NormedSpace.exp_series_hasSum_exp'`, continuous linear
  evaluation and `HasSum.unique`.
- `pureDensityState`: a local representation of the standard construction
  (标准构造的本地表示). From `v* v=1`, set `rho=vv*`.
  For every x, `x* rho x=|v* x|^2 >= 0`, and
  `tr(rho)=v* v=1`. The local `DensityState` packages these two properties
  of the existing rank-one matrix; it introduces no new pure-state law.
- `energy_eigenstate_variance_zero`: the trace identity gives
  `Re tr(rho A)=Re(v*Av)`. If `Hv=Ev`, normalized v and real E give
  the first moment E. Also `H^2v=E^2v`, so the second moment is E^2;
  subtracting the squared first moment gives zero. The Lean theorem does
  not assume Hermiticity of H: this algebra remains valid for any complex
  matrix with the stated real eigenvalue and normalized vector. Its
  interpretation as an energy-observable variance is on the Hermitian
  domain; nonnegative variance for arbitrary matrices is not asserted.

## What this note does and does not attest

Attested by this repository's own retrieval: Higham's chapter metadata,
Taylor and exponential formulas, Preskill's formulas and pure-state
paragraph at the locations above, and the local declaration boundaries.
The series-evaluation and moment-subtraction bridges are explicit here.

The round-19 classification is received from issue #6298. Treating the
2006 chapter as the later standalone book, attributing these exact Lean
signatures to either source, or claiming priority would be
`ASSUMED-UNVERIFIED`; none is asserted. The existing Citation for
`energy_eigenstate_stationary` is outside this correction.
