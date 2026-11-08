---
bibkey: hanna2025a3894congruences
authors: Paul D. Hanna
year: 2025
title: "OEIS A389474, A389475 and A389472: composition-series congruences"
doi: null
url: https://oeis.org/A389474
claim: "The normalized composition series in A389474 and A389475 and the sequence A389472 satisfy the five quoted coefficient congruences."
strata_touched:
  - D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine
  - D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree
  - D5/S1/Recurrence/Parity/SquareCubeSubstitutionThreeIndexModThree
license: citation-only
triage: anchor
---

# Hanna's composition-series congruences

## Verified locator

Source: https://oeis.org/A389474

Related sources: https://oeis.org/A389475 and https://oeis.org/A389472.
The OEIS entries are unpaginated and have no identified DOI or arXiv source.
A389474 is revision 11, published 2025-10-26; the author line is Paul D. Hanna, Oct 24 2025.

## Statements

> G.f. A(x) satisfies A( x^2 + 2*x^3 + 2*A(x)^2 ) = 3*A(x)^2.

> G.f. A(x) = Sum_{n>=1} a(n)*x^n satisfies the following formulas.

> (1) A( x^2 + 2*x^3 + 2*A(x)^2 ) = 3*A(x)^2.

> G.f.: A(x) = x + x^2 + 4*x^3 + 14*x^4 + 104*x^5 + 488*x^6 + 3291*x^7 + 18141*x^8 + 127527*x^9 + 790427*x^10 + ...

> (3) [x^n] A(x)^2 == 0 (mod 9) for n > 3 (conjecture).

> (4) [x^n] A(x)^(3*k) - A(x^3)^k == 0 (mod 3) for n >= 1 and k >= 1 (conjecture).

> G.f. A(x) satisfies A(3*x^2) = 2*x^2 + A(x)^2 - 2*A(x)^3.

> (1) A(3*x^2) = 2*x^2 + A(x)^2 - 2*A(x)^3.

> G.f.: A(x) = x + x^2 + 7*x^3 + 17*x^4 + 147*x^5 + 445*x^6 + 2199*x^7 + 9993*x^8 + 61837*x^9 + 281417*x^10 + 1515387*x^11 + 7844861*x^12 + ...

> (4.a) A(x)^3 == A(x^3) (mod 3) (conjecture).

> (4.b) A(x)^2 == x^2 + 2*A(x^3) (mod 3) (conjecture).

> G.f. satisfies A(x) = A(x^2 + x^3)/x^2 - 1.

> (1) A(x) = A(x^2 + x^3)/x^2 - 1.

> G.f.: A(x) = x + x^2 + 2*x^3 + 3*x^4 + 6*x^5 + 9*x^6 + 14*x^7 + 24*x^8 + 42*x^9 + 72*x^10 + 114*x^11 + 179*x^12 + ...

> Conjecture: a(3*n-1) = 0 (mod 3) for n > 1.

The series in A389474 and A389475 have zero constant coefficient and linear coefficient one.
Congruences of rational coefficients are expressed by equality to an integer multiple of the modulus.
The A389472 sequence uses its existing integer recurrence, including the seed a(2)=1;
the functional equation alone does not fix that seed. All quantified indices are natural numbers.

The all-index derivations use integral triangular lifting, normalized coefficient uniqueness,
the characteristic-three Frobenius identity, an invertible constant-one factor for A389474,
and Lucas congruences with strong descent for A389472.

Literature-screen completeness and publication priority are ASSUMED-UNVERIFIED.
The source identifies conjectural lines; it does not supply a kernel proof.
