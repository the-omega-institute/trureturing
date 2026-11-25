---
bibkey: hunsucker1971binaryfoursquares
authors: John L. Hunsucker
year: 1971
title: "Primitive representation of a binary quadratic form as a sum of four squares"
doi: 10.4064/aa-19-4-321-325
url: https://doi.org/10.4064/aa-19-4-321-325
claim: "Section 1 attributes to Mordell the equivalence between four linear squares and the three-square determinant condition for primitive positive definite integral binary forms."
strata_touched:
  - D5/S3/Quantum/AURICOmega/RationalUnitTripleGram
license: citation-only
triage: anchor
---

# The four-square representation of a binary quadratic form

Section 1, p. 321, attributes to Mordell the criterion for writing a positive
definite primitive integral form $pX^2+2rXY+qY^2$ as four squares of integral
linear forms. Its determinant $pq-r^2$ must avoid $4^k(8m+7)$, which is
Legendre's three-square condition for that positive integer.
[Hunsucker, §1](https://doi.org/10.4064/aa-19-4-321-325) ·
[Mordell's quaternion proof](https://doi.org/10.1093/qmath/os-8.1.58)

In a three-point unit Gram matrix, align the first vector with an axis.
The remaining binary form has $p=1-a^2$, $q=1-b^2$ and $r=c-ab$.
Its determinant is the determinant of the original Gram matrix. For positive
determinant, scaling to a primitive integral form changes the determinant by
a rational square factor. Each integral linear-square representation rescales
to a rational one after multiplying the primitive form by its positive rational
content. Such a scalar times four squares is again four rational squares by
Lagrange's theorem and quaternion norm multiplicativity. The Lean proof uses the
rational quaternion reconstruction directly and includes singular residuals.
