# Same Prime Scale Redundancy

## Abstract

Adjacent scales at one base are redundant, unlike two distinct prime readings.

**Theorem 1.1 (The old layer is an explicit projection of the new layer).**

$$\forall p, k \in \mathbb{N},\\{}q_{p, k} = rho_{p, k+1, k} \circ q_{p, k+1}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy.old_layer_factors_through_new` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The readout and projection are the existing primePowerReadout and primePowerProjection. The latter is Mathlib's ZMod.castHom.

The imported vertical inverse-system theorem supplies compatibility at k <= k + 1. No primality assumption is used: the statement holds for every natural base, including zero and one.

**Theorem 1.2 (The adjacent joint and high layer have identical fibers).**

$$\forall p, k \in \mathbb{N}, x, y \in \mathbb{Z},\\{}A_{p, k}(x) = A_{p, k}(y) \iff q_{p, k+1}(x) = q_{p, k+1}(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy.adjacent_joint_same_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of joint readings implies equality of their second coordinates. Conversely, equality at the high layer descends through the explicit projection to equality at the old layer.

Thus the product interface induces exactly the high layer's fiber relation, not merely a one-way refinement.

**Lemma 1.3 (Precision zero is the single residue class).**

$$\forall p \in \mathbb{N}, x, y \in \mathbb{Z}, q_{p, 0}(x) = q_{p, 0}(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy.zero_precision_readout_is_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At k = 0 the modulus is p to the zero, hence one. ZMod 1 is a singleton, so every pair of integers lies in the same fiber.

**Lemma 1.4 (The first two binary fibers are congruence modulo two and four).**

$$\forall x, y \in \mathbb{Z},\\{}(q_{2, 1}(x) = q_{2, 1}(y) \iff 2 \mid y-x) \land (q_{2, 2}(x) = q_{2, 2}(y) \iff 4 \mid y-x).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy.two_adjacent_precision_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For base two, equality at precision one means divisibility of the difference by two. Equality at precision two means divisibility by four. These are the concrete adjacent fibers requested.

**Lemma 1.5 (Repeating one prime gives a redundant diagonal pair).**

$$\forall p, k \in \mathbb{N},\\{}\operatorname{ker}\left(H_{p, p, k}\right) = \operatorname{ker}\left(q_{p, k}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy.repeated_prime_pair_same_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the two prime labels coincide, the same-level pair repeats one coordinate. Its fiber relation is exactly the single coordinate's fiber relation.

**Theorem 1.6 (The mod two and mod three joint is strictly finer than either sensor).**

$$\operatorname{ker}\left(H_{2, 3, 1}\right) \subset \operatorname{ker}\left(q_{2, 1}\right) \land \operatorname{ker}\left(H_{2, 3, 1}\right) \subset \operatorname{ker}\left(q_{3, 1}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy.different_prime_joint_strictly_finer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint kernel at p = 2, q = 3, and k = 1 is strictly contained in each single-coordinate kernel.

Zero and two collide modulo two but separate modulo three. Zero and three collide modulo three but separate modulo two. These two named witnesses prove strictness in both directions.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy.adjacent_joint_same_fiber`
- Truth anchor: `D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy.different_prime_joint_strictly_finer`
- Truth anchor: `D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy.old_layer_factors_through_new`
- Truth anchor: `D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy.repeated_prime_pair_same_fiber`
- Truth anchor: `D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy.two_adjacent_precision_fibers`
- Truth anchor: `D5/S3/Factorization/PrimePowers/SamePrimeScaleRedundancy.zero_precision_readout_is_constant`
- Dependency: [D5/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy](PrimeBudgetReadoutDichotomy.md)
