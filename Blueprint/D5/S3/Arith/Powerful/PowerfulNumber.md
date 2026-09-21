# Powerful numbers and their square-cube representation

## Abstract

A positive integer in which every prime divisor occurs to order at least two is a square times a cube with squarefree cube root.

The powerful condition is stated on prime divisors rather than on exponents, so it reads directly off divisibility. The representation converts it into a shape from which the density of powerful numbers and their appearance in additive questions can be read.

**Definition 1.1 (Powerful integers).**

Lean statement: `D5/S3/Arith/Powerful/PowerfulNumber.Powerful`

*Formalization.* `D5/S3/Arith/Powerful/PowerfulNumber.Powerful` (`✓ std3`).

*Citation.* Solomon W. Golomb (1970). *Powerful numbers*. DOI: [10.1080/00029890.1970.11992654](https://doi.org/10.1080/00029890.1970.11992654).

*Commentary.*

Powerful n holds when n is nonzero and, for every prime p dividing n, the square of p also divides n.

**Theorem 1.2 (The square-cube representation).**

Lean statement: `D5/S3/Arith/Powerful/PowerfulNumber.golomb_representation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Powerful/PowerfulNumber.golomb_representation` (`✓ std3`). ∎

*Citation.* Solomon W. Golomb (1970). *Powerful numbers*. DOI: [10.1080/00029890.1970.11992654](https://doi.org/10.1080/00029890.1970.11992654).

*Commentary.*

For n at least one and powerful there are naturals a and b with n equal to a squared times b cubed and with b squarefree. Mathlib decomposes n as d squared times c with c squarefree. For a prime p occurring in c, the squarefree condition puts its exponent in c at one, while the powerful condition puts its exponent in n at least at two; since that exponent is twice its exponent in d plus its exponent in c, the exponent in d is at least one. Comparing exponents at every prime gives c dividing d, and writing d as e times c turns d squared times c into e squared times c cubed, which is the stated representation with b equal to c. Uniqueness of the squarefree part is not claimed.

## References

- Truth anchor: `D5/S3/Arith/Powerful/PowerfulNumber.Powerful`
- Truth anchor: `D5/S3/Arith/Powerful/PowerfulNumber.golomb_representation`
