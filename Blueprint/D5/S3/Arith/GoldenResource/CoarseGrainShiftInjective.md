# Forward-Shift Injectivity of the Golden Observation

## Abstract

Agreement at every forward shift determines the index seen by the golden observation.

**Theorem 1.1 (Forward-shift agreement determines the index).**

$$\forall a, c \in \mathbb{N}, (\forall t \in \mathbb{N}, b(a+t) = b(c+t)) \implies a = c$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/CoarseGrainShiftInjective.b_shift_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The function b is the reused frozen golden exponent observation from GoldenDivisorLanguage. It is defined there by b(a) equal to fib of greatestFib(a plus one), minus one. The observation is monotone, but it is not asserted to be strictly monotone.

For natural indices a and c, equality of b(a plus t) and b(c plus t) for every natural offset t forces a and c to be equal. For unequal indices, a later Fibonacci endpoint is fixed by the larger shifted index while the smaller shifted index remains strictly below it.

This is the additive equality stated as Theorem 2.1 in the source text. It does not state the multiplicative Corollary 2.2 or reconstruct an integer from a family of prime exponents.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/CoarseGrainShiftInjective.b_shift_injective`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenDivisorLanguage](GoldenDivisorLanguage.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenFixedPoint](GoldenFixedPoint.md)
