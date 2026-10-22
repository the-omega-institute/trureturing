# Definitions and supremum

## Abstract

Elliptic remainder parameter exponent

**Definition 1.1 (Coefficient polynomial).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Defs.g6`

*Formalization.* `D5/S3/Analytic/EllipticTailExponent/Defs.g6` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial g6 k a is a times the product of a+j and the product of 1-a+j, each over 0 <= j < k. Both products are one when k=0.

**Definition 1.2 (Finite truncation).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Defs.S`

*Formalization.* `D5/S3/Analytic/EllipticTailExponent/Defs.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial S n a sums g6 k a divided by (k+1)(k!)^2 for 0 <= k <= n. Its derivative is the ordinary real derivative of this finite polynomial.

**Definition 1.3 (Remainder exponent).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Defs.lambda10`

*Formalization.* `D5/S3/Analytic/EllipticTailExponent/Defs.lambda10` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function lambda10 n a is a/(1-a) times the quotient whose numerator is sin(pi a)+pi(1-a)cos(pi a)-pi(1-a)^2 deriv(S n)(a) and whose denominator is sin(pi a)-pi(1-a)S n a.

**Definition 1.4 (Supremum for every truncation).**

Lean statement: `D5/S3/Analytic/EllipticTailExponent/Defs.claim`

*Formalization.* `D5/S3/Analytic/EllipticTailExponent/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, including zero, two is the least upper bound of the image of lambda10 n on the real interval (0,1/2].

## References

- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Defs.S`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Defs.claim`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Defs.g6`
- Truth anchor: `D5/S3/Analytic/EllipticTailExponent/Defs.lambda10`
