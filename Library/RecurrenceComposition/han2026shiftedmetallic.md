---
bibkey: han2026shiftedmetallic
authors: Guo-Niu Han, Emmanuel Pedon
year: 2026
title: "Hankel determinants for the (n+2)-shifted q-metallic numbers"
doi: 10.48550/arXiv.2610.36132
url: https://arxiv.org/abs/2610.36132v1
claim: "Conjecture C: integer-valued rational residue polynomials for all higher shifted q-metallic Hankel determinants."
strata_touched:
  - D5/S3/Combinatorics/MetallicHankel/MetallicHankelQuasipolynomialDefs
  - D5/S3/Combinatorics/MetallicHankel/MetallicHankelResiduePolynomials
license: citation-only
triage: anchor
---

# Han and Pedon, higher-shift metallic Hankel quasipolynomials

## Verified locator

DOI: [10.48550/arXiv.2610.36132](https://doi.org/10.48550/arXiv.2610.36132).
The cited version is [arXiv:2610.36132v1](https://arxiv.org/abs/2610.36132v1).
In the [versioned full text](https://arxiv.org/html/2610.36132v1), Conjecture C
in the introduction states the parity-dependent period and integer-valued
residue-polynomial identity for every m>=0. Equations (1.4) and (1.5) define
the shifted Hankel determinants and the empty determinant; equation (2.13)
characterises the metallic power series. The source carries the arXiv.org
perpetual non-exclusive license; this note retains citation-only use.

## Formal scope

Conjecture C in the introduction prescribes residue polynomials for every metallic parameter n>=1 and shift ell>=n+3. Equation (2.13) defines the integral series by constant coefficient one and q Phi^2+((1+q^n)(1-q)-q[n]_q)Phi=1. Equations (1.4) and (1.5) define Delta_j^(ell)=det([q^(ell+a+b)]Phi) on 0<=a,b<j, with empty determinant one.

The allowed period is rho=2n(n+1) for even n and rho=4n(n+1) for odd n. For every residue 0<=r<rho there is Q_r in Q[X] with Delta_(r+m rho)^(ell)=Q_r(m) for every natural m, including zero. Each Q_r takes integer values at every integer, including negative ones. There is no eventual qualification, excluded initial size, target or neighboring-minor invertibility premise, degree bound or minimal-period requirement. The formal claim retains existence of a metallic series for every n>=1 as a conclusion and quantifies over every satisfying series.

The original preregistration is issue #23253. The exact statement is `Trureturing.OpenProblems.HanPedonShiftedQMetallicHankel.claim` in `MetallicHankelQuasipolynomialDefs`, and its settling declaration is `MetallicHankelResiduePolynomials.result`. The dossier is `Problems/han-pedon-metallic-hankel-quasipolynomial.md`. The proof combines the identical normal continuants, arbitrary endpoint jets, an ordered complementary boundary determinant valid at the first term, and backward integer-value propagation. These are repository-derived proofs of the cited assertion; the paper is the source of the conjecture. Source-selection/current-binding audit gaps are tracked separately under issue #23562.

The earlier paper arXiv:2502.05993v2 is a different source, recorded under `han2025hankel`; its Conjecture E concerns bounded-shift periodicity and higher-shift unboundedness.
