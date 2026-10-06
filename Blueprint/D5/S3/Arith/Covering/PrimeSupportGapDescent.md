# Prime-Support Gap Descent

## Abstract

A count-then-sum minimal distinct odd cover cannot omit a smaller prime from its common-modulus support while containing a larger prime.

**Theorem 1.1 (Minimal covers have no prime-support gap).**

Lean statement: `D5/S3/Arith/Covering/PrimeSupportGapDescent.no_gap_in_prime_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/PrimeSupportGapDescent.no_gap_in_prime_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be an odd distinct covering system that is minimal first in its number of classes and then in the sum of its moduli. If p and q are odd primes with p < q, p does not divide the common modulus, and q does divide it, then the stated minimality hypotheses are inconsistent.

The q-divisibility of the common least common multiple supplies a modulus divisible by q. Sum minimality turns that modulus into a pure q class. Since p divides no original modulus, the adjacent profile exchange with zero p- and q-heights produces a covering system with fewer classes, contradicting class-count minimality.

The result is conditional on the stated minimality and support hypotheses; it is not an unrestricted covering theorem.

## References

- Truth anchor: `D5/S3/Arith/Covering/PrimeSupportGapDescent.no_gap_in_prime_support`
- Dependency: [D5/S3/Arith/Congruence/ConditionalComparison/AdjacentProfileExchange](../Congruence/ConditionalComparison/AdjacentProfileExchange.md)
- Dependency: [D5/S3/Arith/Covering/PrimeFactorPureClass](PrimeFactorPureClass.md)
