# Dirichlet Unit Completion

## Abstract

Dirichlet coordinates split unit recovery into a free lattice and finite torsion.

**Definition 1.1 (Integer coordinates in the logarithmic unit lattice).**

Lean statement: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.ArchimedeanLatticeCoordinates`

*Formalization.* `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.ArchimedeanLatticeCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integer coordinates in the logarithmic unit lattice.

**Definition 1.2 (Torsion and archimedean coordinates).**

Lean statement: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.UnitCompletionCoordinates`

*Formalization.* `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.UnitCompletionCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Torsion and archimedean coordinates.

**Definition 1.3 (Reconstruction from the two coordinate layers).**

Lean statement: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.unitCompletionReconstruction`

*Formalization.* `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.unitCompletionReconstruction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reconstruction from the two coordinate layers.

**Theorem 1.4 (Unit rank is r1 plus r2 minus one).**

$$rank(K) = r_1(K) + r_2(K) - 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.unit_rank_eq_real_add_complex_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of infinite places is r1 plus r2. Mathlib's Dirichlet rank is one less than that count; no prime-distribution statement is used.

**Theorem 1.5 (Two-layer reconstruction is bijective).**

$$Reconstruct(K): mu(K) \times \mathbb{Z}^{rank(K)} \to O(K)^{\times} \text{is bijective}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.unitCompletionReconstruction_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's unique Dirichlet decomposition supplies surjectivity and injectivity for the reconstruction homomorphism.

**Definition 1.6 (The unit group as torsion times a free integer lattice).**

Lean statement: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.unitCompletionMulEquiv`

*Formalization.* `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.unitCompletionMulEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unit group as torsion times a free integer lattice.

**Theorem 1.7 (The rational signature is one real and zero complex places).**

$$(r_1(\mathbb{Q}), r_2(\mathbb{Q})) = (1, 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.rational_archimedean_signature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unique infinite place of the rationals is real, so the rational signature is exactly the pair one and zero.

**Theorem 1.8 (The rational free unit rank vanishes).**

$$rank(\mathbb{Q}) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.rational_unit_rank_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution of the rational signature into the rank formula leaves no free archimedean coordinate.

**Theorem 1.9 (Rational torsion is exactly a sign choice).**

$$\forall zeta \in mu(\mathbb{Q}), zeta = 1 \lor zeta = -1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.rational_torsion_unit_eq_one_or_neg_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every rational root-of-unity coordinate is one or minus one. Thus the remaining torsion layer is a single sign bit.

**Theorem 1.10 (Fixed finite data leaves exactly the sign bit).**

$$\forall x, y \in \mathbb{Q}, nu(x) = nu(y) \Rightarrow (x = y \iff \operatorname{sgn}(x) = \operatorname{sgn}(y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.rational_two_layer_recovery_iff_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete finite profile from section 178 fixes absolute value. Equality then becomes equivalent to equality of signs, including at zero.

**Theorem 1.11 (Imaginary quadratic fields have unit rank zero).**

$$r_1(K) = 0 \land r_2(K) = 1 \Rightarrow rank(K) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.imaginary_quadratic_unit_rank_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A signature with no real place and one complex pair gives rank zero.

**Theorem 1.12 (Imaginary quadratic units are all torsion).**

$$(r_1(K), r_2(K)) = (0, 1) \Rightarrow \forall u \in O(K)^{\times}, u \in mu(K).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.imaginary_quadratic_units_are_torsion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The free product is indexed by an empty type, so every unit is its finite root-of-unity coordinate.

**Theorem 1.13 (Real quadratic fields have unit rank one).**

$$r_1(K) = 2 \land r_2(K) = 0 \Rightarrow rank(K) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.real_quadratic_unit_rank_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two real places and no complex pair give one free integer coordinate.

**Definition 1.14 (The sole unit in the real quadratic fundamental system).**

Lean statement: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.realQuadraticFundamentalUnit`

*Formalization.* `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.realQuadraticFundamentalUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sole unit in the real quadratic fundamental system.

**Theorem 1.15 (Real quadratic units are torsion times powers of one unit).**

$$(r_1(K), r_2(K)) = (2, 0) \Rightarrow \forall u, \exists zeta \in mu(K), \exists n \in \mathbb{Z}, u = zeta \times epsilon^{n}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.real_quadratic_unit_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rank-one fundamental system has one member. Every unit is therefore a root of unity times an integer power of this fundamental unit.

## References

- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.ArchimedeanLatticeCoordinates`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.UnitCompletionCoordinates`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.imaginary_quadratic_unit_rank_zero`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.imaginary_quadratic_units_are_torsion`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.rational_archimedean_signature`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.rational_torsion_unit_eq_one_or_neg_one`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.rational_two_layer_recovery_iff_sign`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.rational_unit_rank_zero`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.realQuadraticFundamentalUnit`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.real_quadratic_unit_decomposition`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.real_quadratic_unit_rank_one`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.unitCompletionMulEquiv`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.unitCompletionReconstruction`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.unitCompletionReconstruction_bijective`
- Truth anchor: `D5/S3/Factorization/Embeddings/DirichletUnitCompletion.unit_rank_eq_real_add_complex_sub_one`
- Dependency: [D5/S3/Factorization/Embeddings/RationalValuationRecovery](RationalValuationRecovery.md)
