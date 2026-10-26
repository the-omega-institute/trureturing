---
bibkey: hanna2023bilateral
authors: Paul D. Hanna
year: 2023
title: "OEIS A363558, A363559, A363561 and A363569: bilateral power sums"
doi: null
url: https://oeis.org/A363558
claim: "Eight conjectures on the coefficients of Sum_{n=-oo..+oo} x^n * (c + x^n)^(2*n), at powers of two and primes greater than three, for c = 2, 3, sqrt(2), i."
strata_touched:
  - D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo
  - D5/S1/Recurrence/HannaBilateral/OeisA363558Prime
  - D5/S1/Recurrence/HannaBilateral/OeisA363559PowerOfTwo
  - D5/S1/Recurrence/HannaBilateral/OeisA363559Prime
  - D5/S1/Recurrence/HannaBilateral/OeisA363561PowerOfTwo
  - D5/S1/Recurrence/HannaBilateral/OeisA363561Prime
  - D5/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo
  - D5/S1/Recurrence/HannaBilateral/OeisA363569Prime
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A363558

Related source entries: https://oeis.org/A363559, https://oeis.org/A363561,
https://oeis.org/A363569. These are unpaginated OEIS entries; the statements
below occur in their NAME and FORMULA fields.

## Source statements

- A363558, NAME: "Expansion of g.f. A(x) = Sum_{n=-oo..+oo} x^n * (2 + x^n)^(2*n)."
- A363558, FORMULAS: "a(2^n) = 4^(2^n) for n > 0 (conjecture)." "a(p) = p*2^(p-1) + 4^p for primes p > 3 (conjecture)."
- A363559, NAME: "Expansion of g.f. A(x) = Sum_{n=-oo..+oo} x^n * (3 + x^n)^(2*n)."
- A363559, FORMULAS: "a(2^n) = 9^(2^n) for n > 0 (conjecture)." "a(p) = p*3^(p-1) + 9^p for primes p > 3 (conjecture)."
- A363561, NAME: "G.f.: Sum_{n=-oo..+oo} x^n * (sqrt(2) + x^n)^(2*n)."
- A363561, FORMULAS: "a(2^n) = 2^(2^n) for n > 0 (conjecture)." "a(p) = p*2^((p-1)/2) + 2^p for primes p > 3 (conjecture)."
- A363569, NAME: "Expansion of g.f. A(x) = Sum_{n=-oo..+oo} x^n * (i + x^n)^(2*n), where i^2 = -1."
- A363569, FORMULAS: "a(2^n) = 1 for n > 0 (conjecture)." "a(p) = p*(-1)^((p-1)/2) - 1 for primes p > 3 (conjecture)."

## Coefficients and scope

The formal coefficients are complex numbers. The nonnegative integer terms
are expanded as polynomials. For a negative index -k, with k positive, the
summand is X^(2*k^2-k) times the formal inverse of (1+c*X^k)^(2*k).
At degree m only nonnegative indices at most m and negative magnitudes at
most m can contribute. No analytic convergence assertion is needed.

The coefficient formulas at positive dyadic powers hold for every complex c:
coeffA(c,2^N)=c^(2^(N+1)) for N>0. For prime p>3, the formula is
coeffA(c,p)=p*c^(p-1)+c^(2*p). The displayed OEIS conjectures specialize
these identities to the four parameters above. Completeness of the
literature screen is ASSUMED-UNVERIFIED.

## Numerical evidence

The independent experiment is in the private repository
the-omega-institute/trureturing-experiments at commit
1133ccd5c01a70de0997056d1ec6bdbb3c8b6a32, under
docs/reports/oeis-a363558-a363559-a363561-a363569-bilateral-power-sums/.
Its check.py has SHA-256
b39e40018fd0826204c5ecc5d01373129e88b32b0b1556b44e8631c2b0431c04.
The recorded command `python3 check.py 300 12` exits 0 with RESULT PASS.
It checks symbolic coefficients through degree 14, dyadic exponents 1
through 12 and primes at most 300; these finite readings are distinct from
the universal Lean statements.
