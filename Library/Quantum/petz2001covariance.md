---
bibkey: petz2001covariance
authors: Denes Petz
year: 2001
title: Covariance and Fisher information in quantum mechanics
doi: null
url: https://arxiv.org/abs/quant-ph/0106125
claim: Centering both arguments of the symmetric trace form gives quantum covariance; real additivity and nonnegative variance on self-adjoint observables are standard direct consequences.
strata_touched:
  - D5/S3/Quantum/Information/CovarianceSumBound
license: citation-only
triage: anchor
---

# Centering the symmetric trace form

## Verified locator

The exact upstream locator is:
https://arxiv.org/abs/quant-ph/0106125

The arXiv abstract page was retrieved successfully. It gives the title and
author above and arXiv:quant-ph/0106125v1, submitted 22 June 2001. Its metadata
also lists the later journal DOI; this note binds the arXiv record only.

The round-17 seat reports section 2, equation (16), as the symmetric bilinear
form on self-adjoint matrices

    φ_D[A,B] = ½ Tr D(AB + BA).

The interior locator is seat-reported and was not checked against the PDF here.

## Scope of the dependency

Let D ≥ 0 have trace one and put a = Tr DA and b = Tr DB for self-adjoint A,B.
Expanding the centered form gives

    φ_D[A−aI, B−bI] = ½ Tr D(AB+BA) − ab = Cov_D(A,B).

Trace linearity and linearity of the mean imply that centering B+C is the sum
of the centered B and C. Hence Cov_D(A,B+C) = Cov_D(A,B) + Cov_D(A,C).
Symmetry and Cov_D(A,A) = Var_D(A) follow by exchanging or identifying the
arguments. With X = A−aI self-adjoint,

    Var_D(A) = Tr D X² = Tr X D X ≥ 0,

because X D X is positive semidefinite. This uses trace cyclicity and positivity;
it does not require A and B to commute or D to be invertible. The finite matrix
extension to singular states is justified by this argument, without asserting
that every information metric in the source has that scope.

The repository's definitions are also total on non-self-adjoint matrices.
Real trace linearity proves its additivity identity on that larger domain too,
but this is an algebraic extension of the convention, not an assertion that
the source's observable-domain bilinear form has exactly the same domain.
The variance positivity theorem in Lean explicitly requires self-adjointness.
The star-based literature convention and the real-part distinction are detailed
in `D5/L/Quantum/gibilisco2007covariance`.

## What this note does and does not attest

Attested by this repository's own retrieval: the arXiv record title, author,
identifier and v1 submission date above.

Not attested here: section 2 and equation (16) in the PDF. That locator and its
formula are the round-17 seat's report, relayed in the implementation brief and
issue #6298, and remain `ASSUMED-UNVERIFIED` as interior source readings.
The centering, additivity and positivity derivations are written out here;
the note does not invent separate named theorems for those consequences.
No priority or earliest-appearance claim is made.
