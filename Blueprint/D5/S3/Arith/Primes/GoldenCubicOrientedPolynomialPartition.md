# The monic oriented polynomial factors of a golden cubic probe

## Abstract

Three monic polynomial factors organize the oriented finite-field cubic readouts.

**Theorem 1.1 (The three orientation factors are monic with degrees m minus one, m and m).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicOrientedPolynomialPartition.monic_oriented_polynomial_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicOrientedPolynomialPartition.monic_oriented_polynomial_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a prime greater than three and q=p to a positive integer power. In the quadratic algebra, write the m-th power of X plus the formal square root of minus three as U plus that square root times V, with m=(q-1)/3 in the split case and (q+1)/3 otherwise. The scaling c is minus three in the split case and plus three otherwise; it is the inverse of m in the coefficient ring.

The three factors cV, U-V and U+V are monic with degrees m-1, m and m. Their product is X to the q minus X in the inert case; in the split case multiplication by X squared plus three gives the same polynomial. The Frobenius sign is derived from the cube-root relation, not assumed.

The checked theorem is the exact polynomial factorization and its degree data. Over the actual finite field the displayed product implies disjoint simple roots, and the torus comparison identifies the three oriented fibers. This does not identify the global conductor character, prove an effective prime bound, or solve Wall-Sun-Sun.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicOrientedPolynomialPartition.monic_oriented_polynomial_partition`
