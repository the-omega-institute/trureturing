---
bibkey: trureturing2026fibonacciclippedprofile
authors: trureturing research synthesis
year: 2026
title: Six-interval certificate for the Fibonacci pure-qubit profile
doi: null
url: https://github.com/the-omega-institute/trureturing
claim: Six explicit rational affine functions bound the excess forward hockey-stick profile for unit pure-qubit triples, including dependent preparations.
strata_touched:
  - D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile
license: Apache-2.0
triage: anchor
---

# Six-interval certificate for the Fibonacci pure-qubit profile

## Verified locator

Sections 1–3 of the research derivation `fibonacci-positive-triple-analytic-answer.txt`
(SHA-256 `61113fa360deaca6e5ea22f87dba889236c55c1dba3da64e08666bff1240580a`)
give the clipped profile and six sign certificates. The Lean proof is repository-derived.
[trureturing](https://github.com/the-omega-institute/trureturing)

## Formalization scope

For unit preparations with projections \(P_1,P_2,P_3\), set
\(b=66t-88\), \(c=15t-25\), \(d=28-12t\), and \(w=b+c+d\).
Write \(X=1-|\langle\psi_1,\psi_2\rangle|^2\),
\(Y=|\langle\psi_1,\psi_3\rangle|^2\), and
\(Z=|\langle\psi_2,\psi_3\rangle|^2\). The benchmark identifies the first
two rays and makes the third orthogonal. The following bounds are for the
trace of the positive part of \(-bP_1-cP_2+dP_3\) minus its benchmark value.

| Interval | Upper bound |
| --- | --- |
| \([4/3,113/81]\) | \(b^2X/d+bZ\) |
| \([113/81,22/15]\) | \(-bcX/w-(97/100)(b+c)Y-cdZ/w\) |
| \([22/15,5/3]\) | \(-bcX/w-bdY/w-cdZ/w\) |
| \([5/3,9/5]\) | \(-(53/55)bcX/w-(24/25)bdY/w\) |
| \([9/5,2]\) | \(-(53/55)bcX/w-(d-(53/55)bc/w)Y\) |
| \([2,7/3]\) | \(-dX\) |

On the first interval the benchmark is positive semidefinite. The trace
and determinant quadratic bounds the negative spectral contribution using
\(0\le b\le d\). On the remaining intervals the discriminant is
\(w^2+4N\), with \(N=-bcX-bdY-cdZ\). Each candidate \(L\) satisfies
\(N\le wL\), \(L\ge -(b+c)\), and \(L\ge-d\). Thus
\(w+2L\ge|d-b-c|\) and \((w+2L)^2\ge w^2+4N\). The six polynomial
sign checks follow from factorizations, endpoint values, and endpoint
derivatives.
