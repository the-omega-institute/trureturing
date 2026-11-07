# Ordinary Euler Product

## Abstract

Ordinary partitions identify the actual reciprocal Euler product and prove strict all-degree positivity.

Mathlib Nat.Partition.hasProd_powerSeriesMk_card_restricted is used with predicate True under the actual discrete rational T2 topological ring structure. Its supplier is Weiyi Wang, Apache 2.0. Mathlib pentagonalSeries is the actual Euler product. These are ordinary positive parts, with no odd-part restriction.

**Definition 1.1 (partitionSeries).**

Lean statement: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.partitionSeries`

*Formalization.* `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.partitionSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete ordinary partition count series, using the unrestricted predicate True.

**Theorem 1.2 (coeff_partitionSeries_ge_one).**

Lean statement: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_partitionSeries_ge_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_partitionSeries_ge_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural degree, including zero, an ordinary partition exists, so its coefficient is at least one.

**Theorem 1.3 (partitionSeries_mul_euler).**

Lean statement: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.partitionSeries_mul_euler`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.partitionSeries_mul_euler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordinary partition series times the actual pentagonal Euler product equals one, by actual topological products and the geometric factor identity.

**Theorem 1.4 (euler_constant_one).**

Lean statement: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.euler_constant_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.euler_constant_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual pentagonal Euler series has constant coefficient one.

**Theorem 1.5 (partitionSeries_eq_euler_inverse).**

Lean statement: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.partitionSeries_eq_euler_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.partitionSeries_eq_euler_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete ordinary partition series equals the unit reciprocal of the actual Euler product.

**Theorem 1.6 (coeff_mul_nonnegative).**

Lean statement: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_mul_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_mul_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite convolution preserves coefficientwise nonnegativity.

**Theorem 1.7 (coeff_pow_nonnegative).**

Lean statement: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_pow_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_pow_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural power of a coefficientwise nonnegative rational power series has nonnegative coefficients.

**Theorem 1.8 (coeff_mul_ge_right).**

Lean statement: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_mul_ge_right`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_mul_ge_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonnegative series with constant coefficient one preserves a coefficientwise lower bound under complete finite convolution.

**Theorem 1.9 (coeff_euler_inverse_pow_ge_one).**

Lean statement: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_euler_inverse_pow_ge_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_euler_inverse_pow_ge_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive natural power of the actual reciprocal Euler series has every coefficient at least one.

The finite convolution bounds include every natural degree and every positive power. They provide positive partition factors; they do not establish any signed eta-quotient pattern without the exact theta identities, proved separately in CubicThetaCoreProduct and CubicThetaIdentities.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_euler_inverse_pow_ge_one`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_mul_ge_right`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_mul_nonnegative`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_partitionSeries_ge_one`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.coeff_pow_nonnegative`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.euler_constant_one`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.partitionSeries`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.partitionSeries_eq_euler_inverse`
- Truth anchor: `D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.partitionSeries_mul_euler`
