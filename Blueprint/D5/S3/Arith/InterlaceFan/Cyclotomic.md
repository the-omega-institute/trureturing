# Rational values and root orders

## Abstract

Cyclotomic propagation and rational witnesses for interlace certificates.

**Theorem 1.1 (Cosine evaluation of an interlace functional).**

Lean statement: `D5/S3/Arith/InterlaceFan/Cyclotomic.I_eq_eval`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/Cyclotomic.I_eq_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reciprocal-pair evaluation is twice the cosine sum. The interlace functional is its negative half.

**Theorem 1.2 (Evaluation of the reciprocal polynomial).**

Lean statement: `D5/S3/Arith/InterlaceFan/Cyclotomic.I_eq_eval_poly`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/Cyclotomic.I_eq_eval_poly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every certificate index, evaluation at the corresponding standard root of unity equals the real cosine sum. Each coordinate contributes the two monomials with exponents k and n-k. At the middle index for even n these coincide, giving twice the coordinate as the polynomial coefficient.

**Theorem 1.3 (Rational values propagate through an order class).**

Lean statement: `D5/S3/Arith/InterlaceFan/Cyclotomic.rational_const_on_orderClass`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/Cyclotomic.rational_const_on_orderClass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For rational coordinates and a positive darga n, a rational certificate value at one primitive d-th root is the same at every certificate root of order d, where d divides n. Multiplying the certificate value by minus two gives the rational polynomial value. Subtracting that constant gives a polynomial divisible by the d-th cyclotomic polynomial, the minimal polynomial of a primitive d-th root.

**Theorem 1.4 (Rational coordinates realizing an order indicator).**

Lean statement: `D5/S3/Arith/InterlaceFan/Cyclotomic.rational_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/Cyclotomic.rational_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every divisor d of n with n at least two, rational sigma coordinates realize the values obtained by subtracting n times the order-class indicator from the totient of d and dividing by two. The coordinates are Ramanujan sums, with the middle coordinate halved when n is even. The public divisor-sum identity proves integrality by induction on the modulus. Finite geometric sums then give the full Fourier transform: n on primitive roots of order d and zero elsewhere. Removing the constant coefficient subtracts the totient of d. Coefficient reconstruction pairs reciprocal exponents and accounts for the doubled middle monomial.

## References

- Truth anchor: `D5/S3/Arith/InterlaceFan/Cyclotomic.I_eq_eval`
- Truth anchor: `D5/S3/Arith/InterlaceFan/Cyclotomic.I_eq_eval_poly`
- Truth anchor: `D5/S3/Arith/InterlaceFan/Cyclotomic.rational_const_on_orderClass`
- Truth anchor: `D5/S3/Arith/InterlaceFan/Cyclotomic.rational_witness`
- Dependency: [D5/S3/Analytic/Certified/FiniteRamanujanDivisorIdentity](../../Analytic/Certified/FiniteRamanujanDivisorIdentity.md)
- Dependency: [D5/S3/Arith/InterlaceFan/Defs](Defs.md)
