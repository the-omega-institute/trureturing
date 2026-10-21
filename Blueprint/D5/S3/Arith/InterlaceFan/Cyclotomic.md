# Order classes and rational values

## Abstract

Cyclotomic propagation and Ramanujan witnesses for interlace certificates.

**Theorem 1.1 (Cosine evaluation of an interlace functional).**

Lean statement: `D5/S3/Arith/InterlaceFan/Cyclotomic.I_eq_eval`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/Cyclotomic.I_eq_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real evaluation of the reciprocal pair of monomials at a certificate root is twice the cosine sum in the sigma coordinates. The interlace functional is its negative half.

**Theorem 1.2 (Propagation within an order class).**

Lean statement: `D5/S3/Arith/InterlaceFan/Cyclotomic.const_on_orderClass`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/Cyclotomic.const_on_orderClass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a rational polynomial evaluation is invariant between two certificate indices of the same root order, equality of one interlace value propagates to every index in that order class.

**Theorem 1.3 (Ramanujan divisor witness).**

Lean statement: `D5/S3/Arith/InterlaceFan/Cyclotomic.witness`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/Cyclotomic.witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive modulus, the normalized sum of Ramanujan phases over its divisors is the indicator of divisibility. This identity supplies the arithmetic witness values used by the interlace construction.

**Theorem 1.4 (Rational order-class target values).**

Lean statement: `D5/S3/Arith/InterlaceFan/Cyclotomic.witness_values`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/InterlaceFan/Cyclotomic.witness_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a divisor of n, the order-class indicator determines a rational target value for every certificate index. These targets are the data passed to Fourier inversion.

## References

- Truth anchor: `D5/S3/Arith/InterlaceFan/Cyclotomic.I_eq_eval`
- Truth anchor: `D5/S3/Arith/InterlaceFan/Cyclotomic.const_on_orderClass`
- Truth anchor: `D5/S3/Arith/InterlaceFan/Cyclotomic.witness`
- Truth anchor: `D5/S3/Arith/InterlaceFan/Cyclotomic.witness_values`
- Dependency: [D5/S3/Analytic/Certified/FiniteRamanujanDivisorIdentity](../../Analytic/Certified/FiniteRamanujanDivisorIdentity.md)
- Dependency: [D5/S3/Arith/InterlaceFan/Defs](Defs.md)
