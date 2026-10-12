# Exact Five Mode Vectors on the 5040 Six Cell

## Abstract

The finite 5040 six-cell has an exact normalized five-prime vector.

**Theorem 1.1 (Finite explicit window).**

Lean statement: `D5/S3/Arith/Robin/FiveModePrimeWindowExplicit.goldenCell5040_prime_window_explicit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/FiveModePrimeWindowExplicit.goldenCell5040_prime_window_explicit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each of the six values 5040, 10080, 15120, 20160, 30240 and 60480, the theorem supplies u in {0,1,2} and v in {0,1} with n = 5040 * 2^u * 3^v.  Writing d = 13 + u + v, the coordinates in the order (2,3,5,7,83) are (5+u, 3+v, 2, 2, 1)/d, and the visible projection is (4+v, 3, 2)/d.

## References

- Truth anchor: `D5/S3/Arith/Robin/FiveModePrimeWindowExplicit.goldenCell5040_prime_window_explicit`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenDivisorLanguage](../GoldenResource/GoldenDivisorLanguage.md)
