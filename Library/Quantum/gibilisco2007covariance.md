---
bibkey: gibilisco2007covariance
authors: Paolo Gibilisco, Fumio Hiai, Denes Petz
year: 2007
title: Quantum covariance, quantum Fisher information and the uncertainty principle
doi: null
url: https://arxiv.org/abs/0712.1208
claim: Ordinary symmetrized quantum covariance gives the density-state expectation, covariance and variance conventions on self-adjoint observables, with symmetry and self-covariance as direct algebraic consequences.
strata_touched:
  - D5/S3/Quantum/Information/CovarianceSumBound
license: citation-only
triage: anchor
---

# Symmetrized covariance and the observable domain

## Verified locator

The exact upstream locator is:
https://arxiv.org/abs/0712.1208

The arXiv abstract page was retrieved successfully. It gives the title and
three authors above and the submission arXiv:0712.1208v1, dated 7 December 2007.

The round-17 seat reports the ordinary symmetrized covariance in section 2 as
the **unnumbered formula immediately after equation (7)**:

    Cov_D(A,B) = ½ Tr D(A*B + BA*) − (Tr DA*)(Tr DB).

This is not a citation of equation (7) itself. The interior locator and formula
are seat-reported; the retrieval here checks the record metadata, not the PDF.

## Scope of the dependency

For self-adjoint A and B and a positive trace-one matrix D, the means Tr DA and
Tr DB are real. Thus E_D(A) = Re Tr DA is the ordinary expectation, and the
formula reduces to the repository's

    C_D(A,B) = (E_D(AB) + E_D(BA))/2 − E_D(A) E_D(B).

Setting B = A gives Var_D(A) = E_D(A²) − E_D(A)² and C_D(A,A) = Var_D(A).
Exchanging A and B proves symmetry. These are definitions and direct algebraic
consequences of the stated convention, not separately named literature theorems.
The companion note `D5/L/Quantum/petz2001covariance` writes out the centered
bilinear form, additivity and positivity arguments.

The repository defines expectation, covariance and variance for **all** complex
matrices, and its symmetry and self-covariance identities also hold on that
larger domain by the displayed algebra. This extension is the repository's
convention. For non-self-adjoint inputs it is not identified with the paper's
star-based covariance, and variance is not claimed nonnegative there. In
particular, taking separate real parts before multiplying means is not in
general the same as taking the real part of their complex product.

The repository also permits singular density matrices. On the observable domain
the trace formulas and these algebraic identities require only D ≥ 0 and Tr D = 1;
they do not use an inverse. This extension is explicit here, without attributing
the scope of the paper's Fisher-information constructions to the repository.

## What this note does and does not attest

Attested by this repository's own retrieval: the arXiv record title, authors,
identifier and v1 submission date above.

Not attested here: the PDF's section and equation numbering or a page-by-page
check of its interior. The section-2 location **after** equation (7) and the
displayed literature formula come from the round-17 seat as relayed in the
implementation brief and issue #6298. They remain `ASSUMED-UNVERIFIED` as
interior locators. The correspondence and direct algebraic consequences on
self-adjoint observables are written out above; the larger matrix domain is
explicitly delimited. No priority or earliest-appearance claim is made.
