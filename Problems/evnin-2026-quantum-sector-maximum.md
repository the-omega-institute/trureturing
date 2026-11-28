---
slug: evnin-2026-quantum-sector-maximum
bibkey: evnin2026quantumestimates
doi: 10.1088/1751-8121/aebddd
triage: theorem
motivation_gids:
  - D5/S3/Quantum/FockSpace/EvninQuantumSector.top_finite_sector_eigenvalue
---

# Evnin's finite-sector maximum eigenvalue

## Problem

Oleg Evnin, *Quantum estimates for classical polynomial optimization*, arXiv:2607.25445v3, §2.3, Eq. (33), proposes the exact formula

$$
E_{\sigma,\max}^{(N,M)}=\frac{(N-1)(N+2\sigma M)}{2}.
$$

Footnote 1 describes rounding the integer-σ calculations to obtain “a working guess for the exact form of the top eigenvalues”. Equation (30) takes real σ ≥ 1. The formula concerns every nonempty finite sector of particle number N and momentum M in the normalized bosonic occupation basis. [Versioned equation](https://arxiv.org/html/2607.25445v3#S2.E33)

## Motivation

The eigenvalue gives the sharp upper bound for the quantum operator used in the classical polynomial estimate. Attainment requires a nonzero vector in every nonempty sector.

## Gap

Evnin reports the weighted quantum formula from numerical calculations in §2.3 and proves the classical inequality in Appendix B. De Clerck and Evnin prove the unweighted case σ = 1. Issue #35084 records the bounded literature search for a prior quantum proof in the weighted range σ > 1 and records the source coefficient identities. [Unweighted proof](https://arxiv.org/abs/2511.03373v2) · [Issue #35084](https://github.com/the-omega-institute/trureturing/issues/35084)

## Route

The diagonal squared coefficients of the normalized pair annihilators count ordered pairs, with the falling factorial for a repeated mode. The momentum-weighted sum of the diagonal counts gives the proposed energy times the identity. The Raney convolution and Gamma recurrence identify this sum with the diagonal term of a weighted Gram expansion. The resulting defect from the Hamiltonian is positive semidefinite. Each pair difference in the defect annihilates the vector whose occupation amplitude is the product of the square roots of the mode weights raised to their occupation powers, divided by the square roots of the corresponding occupation factorials.

## Falsifier

A nonempty sector with a larger eigenvalue or with the proposed energy absent from the real spectrum would contradict the formula for real σ ≥ 1. The matrix for such a check must use the normalized occupation basis, the ordered creation and annihilation pair indices, the overall factor 1/2 and the Gamma coefficients of Eq. (31).

## Evidence

The Lean theorem `top_finite_sector_eigenvalue` gives Hermiticity, the greatest real spectral value, and a nonzero factorial eigenvector for that value in every nonempty sector. The Hamiltonian is zero for fewer than two particles. The vacuum at positive momentum is empty, while the vacuum at zero momentum and the one-particle sectors have zero energy.

## Triage

Theorem. The proof covers the full real range σ ≥ 1, with the literature-checked weighted range σ > 1 and the known endpoint σ = 1.

## ASSUMED-UNVERIFIED

The priority assessment for σ > 1 is bounded by the sources and search scope documented in issue #35084. It carries no claim about literature outside that search. [Issue #35084](https://github.com/the-omega-institute/trureturing/issues/35084)
