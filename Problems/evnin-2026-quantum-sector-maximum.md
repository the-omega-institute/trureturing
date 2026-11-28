---
slug: evnin-2026-quantum-sector-maximum
bibkey: evnin2026quantumestimates
doi: 10.1088/1751-8121/aebddd
url: https://arxiv.org/html/2607.25445v3#S2.E33
triage: theorem
motivation_gids:
  - D5/S3/Quantum/FockSpace/EvninQuantumSector.top_finite_sector_eigenvalue
---

# Evnin's finite-sector maximum eigenvalue

## Problem

Oleg Evnin, *Quantum estimates for classical polynomial optimization*, arXiv:2607.25445v3, §2.3, Eq. (33), gives
[
E_{sigma,max}^{(N,M)}=rac{(N-1)(N+2sigma M)}2 .
]
Footnote 1 describes rounding the integer-σ calculations to obtain “a working guess for the exact form of the top eigenvalues”. The range from Eq. (30) is real σ ≥ 1. The formula concerns every nonempty sector of particle number N and momentum M. [Versioned equation](https://arxiv.org/html/2607.25445v3#S2.E33)

## Motivation

The eigenvalue gives the sharp upper bound for the quantum operator used in the classical polynomial estimate. Its attainment requires a nonzero vector in every nonempty sector.

## Gap

The source obtains the weighted quantum formula numerically and proves the classical inequality in Appendix B. De Clerck and Evnin prove the unweighted case σ = 1. The scope of the literature search for the weighted quantum result and the prior Raney coefficient formulas is recorded in the registration. [Unweighted proof](https://arxiv.org/abs/2511.03373v2) · [Issue #35084](https://github.com/the-omega-institute/trureturing/issues/35084)

## Route

Use the normalized pair annihilators on the finite occupation sectors. The diagonal squared coefficients count ordered pairs, including the falling factorial for a repeated mode. Summing these counts with momentum weights gives the proposed energy times the identity. The verified Raney convolution and Gamma ratio identify this sum with the diagonal term of a weighted Gram expansion. The resulting defect from the Hamiltonian is positive semidefinite. Its summands vanish on the vector whose occupation amplitude is the product of the mode weights to half the occupation powers divided by the square roots of the occupation factorials.

## Falsifier

A certified larger eigenvalue, or a sector in which the proposed value is absent from the spectrum, contradicts the formula. The source correspondence uses the ordered creation and annihilation pair indices, the overall factor 1/2, and the Gamma coefficients of Eq. (31).

## Evidence

The Lean theorem `top_finite_sector_eigenvalue` proves Hermiticity, the greatest real spectral value, and the nonzero factorial eigenvector on each nonempty sector. The zero operator covers fewer than two particles. For positive momentum the vacuum sector is empty and lies outside the eigenvalue assertion.

## Triage

The mathematical proof gives equality in the quantum upper bound for every allowed real σ, including noninteger values. It uses the common proportional action of all pairs of a fixed momentum on the factorial vector.
