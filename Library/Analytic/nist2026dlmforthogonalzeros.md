---
bibkey: nist2026dlmforthogonalzeros
authors: NIST Digital Library of Mathematical Functions
year: 2026
title: DLMF Section 18.2, General Orthogonal Polynomials
doi: null
url: https://dlmf.nist.gov/18.2
claim: Positive three-term recurrence coefficients give orthogonality by Favard's theorem, and zeros of orthogonal polynomials are real and simple.
strata_touched:
  - D5/S3/Zeros/Jensen/PositiveThreeTermRootReality
license: citation-only
triage: anchor
---

# Positive recurrences and real zeros

## Verified locator

The official source is https://dlmf.nist.gov/18.2.
The source was read on 2026-10-13. Section 18.2(iv), equations
(18.2.11_5)--(18.2.11_6), gives the monic three-term recurrence and
the positivity of its recurrence coefficients. Section 18.2(viii)
states Favard's theorem for this recurrence with positive coefficients.
Section 18.2(vi) states that all zeros of an orthogonal polynomial are
simple and lie in its real interval of orthogonality. It also identifies
the zeros with eigenvalues of the finite Jacobi matrix in (18.2.18).

## Finite repository formulation

The repository's finite scalar formulation has diagonal coefficient zero:

\[
v_0\ne0,\qquad v_1=zv_0,\qquad
v_{k+2}=zv_{k+1}-c_kv_k,\quad c_k>0\quad(k+2\le q).
\]

Writing the corresponding monic recurrence polynomials as
\(P_0=1,P_1=X,P_{k+2}=XP_{k+1}-c_kP_k\) gives
\(v_k=v_0P_k(z)\) through the finite endpoint. Positive coefficients
can be assigned freely beyond this endpoint. Thus the source's
classical zero-reality result applies when \(v_q=0\). The repository
does not claim this conclusion as a new result in the literature.

The Lean proof instead establishes the finite ratio invariant
\(\operatorname{Im}z\operatorname{Im}(v_{k+1}/v_k)>0\)
under a nonreal parameter. It needs no orthogonality measure, matrix
realization, polynomial root enumeration, or premise on the unobserved
tails. Its delivered conclusion is only \(\operatorname{Im}z=0\);
simplicity and interlacing are not asserted.
