# Native scoped implementation

## Abstract

Finite real-endpoint prime Abel suppliers.

Native compiled scope only. This provider retains the original real endpoints and the strict lower-excluded, upper-included interval (y,z]. It supplies finite Abel identities used by the quantitative and finite-tail declarations; it makes no final RH or exact-infimum claim.

**Definition 1.1 (Prime count at a real endpoint).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel.primeCount`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel.primeCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

primeCount t is Nat.primeCounting floor(t), cast to the reals.

**Definition 1.2 (Strict lower and inclusive upper prime interval).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel.primeInterval`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel.primeInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

primeInterval y z is the filtered Finset.Ioc floor(y) floor(z), so a prime tied at y is excluded and a prime tied at z is included.

**Definition 1.3 (Finite prime-square sum).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel.squareSum`

*Formalization.* `D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel.squareSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

squareSum y z sums 1/p^2 over primeInterval y z, with both real endpoints retained.

**Theorem 1.4 (Exact finite Abel identity).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel.finite_prime_square_abel`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel.finite_prime_square_abel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<y and y<=z, squareSum y z equals primeCount z/z^2 - primeCount y/y^2 + 2 times the finite integral of primeCount t/t^3 from y to z. The proof uses the native finite Ioc definition and no infinite tail.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel.finite_prime_square_abel`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel.primeCount`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel.primeInterval`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel.squareSum`
- Dependency: [D5/S3/Arith/Robin/EulerLayerRootCorrection](../EulerLayerRootCorrection.md)
