---
bibkey: cohn1993squareplusthree
authors: J. H. E. Cohn
year: 1993
title: The Diophantine equation x^2+3=y^n
doi: 10.1017/S0017089500009757
claim: The theorem excludes positive integers x,y and n>=3; pages 204-205 give the polynomial three-adic obstruction used here.
strata_touched: []
license: citation-only
triage: anchor
---

# Cohn's direct three-adic obstruction

## Locator

J. H. E. Cohn, *The Diophantine equation x²+3=yⁿ*, Glasgow Mathematical
Journal 35 (1993), 203–206. DOI: 10.1017/S0017089500009757.

Primary publisher content:
https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0017089500009757

The theorem on page 203 concerns positive integers x,y and n≥3.
The extension to arbitrary integer y and e≥2 under x≥2 additionally
requires exponent, sign and square reductions.

Page 203 reduces odd exponents to odd primes and factors in the integers
of Q(sqrt(-3)). The phrase “six units” concerns that integer ring, not all
units of the field. A formal implementation must prove the coprimality
used by the extraction and transfer the PID/UFD structure through the
existing Eisenstein–cyclotomic equivalence. It must not assume the two
conjugate factors are coprime without the elementary 2- and 3-adic checks.

Page 204 treats the exceptional cube units, obtains the binomial equation,
uses a even and 3 not dividing a, and sets xi=a²−1. It displays exactly
the shifted integer polynomial used in `cohnPolynomial`.

Page 205 displays the ODE

    4(T²+5T+4)P'' − 2((2q−3)T+2q−6)P' + q(q−1)P = 0.

The factorial-scaled reformulation uses d_r=r!c_r
and cancellation of 16 modulo powers of 3. This avoids treating negative
powers of 2 in the paper's scaled B_r formula as integer coefficients.
For q≥7 and q=1 modulo 6 the same polynomial argument works without
primality. The Lean candidate uses that uniform statement, the pinned
Mathlib factorial bound, and its exact LTE API. No external classification
theorem or result from this PDF enters as a Lean axiom or hypothesis.

The direct polynomial reformulation formalizes Cohn's classical argument.
It does not include the separate Eisenstein and exponent reductions.
