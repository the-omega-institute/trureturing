# MUB Hadamard Compatibility

## Abstract

Exact Hadamard atlases retain relative gauges when testing four-MUB compatibility.

**Definition 1.1 (Complex square matrices).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.ComplexSquare`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.ComplexSquare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A square matrix over the complex numbers on a coordinate type n.

**Definition 1.2 (Unit squared entry norms).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.EntrywiseUnit`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.EntrywiseUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every entry of a rectangular complex matrix has squared norm one.

**Definition 1.3 (Unnormalized complex Hadamard matrices).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.IsComplexHadamard`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.IsComplexHadamard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a finite coordinate type with decidable equality, every entry has squared norm one and H times its adjoint equals the cardinality times the identity.

**Definition 1.4 (Row and column monomial equivalence).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.HadamardEquivalent`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.HadamardEquivalent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two complex square matrices are related by row and column permutations and multiplication by row and column phases of squared norm one.

**Theorem 1.5 (Reflexivity of Hadamard equivalence).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.hadamardEquivalent_refl`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.hadamardEquivalent_refl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every complex square matrix is Hadamard equivalent to itself.

**Theorem 1.6 (Transitivity of Hadamard equivalence).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.hadamardEquivalent_trans`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.hadamardEquivalent_trans` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equivalence of H to K and of K to L implies equivalence of H to L.

**Theorem 1.7 (Symmetry of Hadamard equivalence).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.hadamardEquivalent_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.hadamardEquivalent_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If H is Hadamard equivalent to K, then K is Hadamard equivalent to H.

**Definition 1.8 (Flat transitions between matrices).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.HadamardUnbiased`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.HadamardUnbiased` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every entry of the adjoint of H times K has squared norm equal to the finite coordinate cardinality.

**Theorem 1.9 (Symmetry of flat transitions).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.hadamardUnbiased_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.hadamardUnbiased_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If H and K have a flat transition in this sense, then K and H do as well.

**Definition 1.10 (Six-coordinate carrier).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.I6`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.I6` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate type is the disjoint sum of two copies of Fin 3.

**Definition 1.11 (Order-six complex matrices).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.Mat6`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.Mat6` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A complex square matrix on the six-coordinate carrier I6.

**Definition 1.12 (Three pairwise unbiased Hadamard matrices).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.FourMUBHadamardWitness`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.FourMUBHadamardWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A witness supplies three order-six complex Hadamard matrices, with a flat transition for every distinct pair.

**Definition 1.13 (Exact atlas contract).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.IsExactHadamardAtlas`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.IsExactHadamardAtlas` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every order-six matrix H, H is complex Hadamard exactly when some atlas entry is Hadamard equivalent to H.

**Definition 1.14 (Compatibility of lifted atlas entries).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.HasLiftedFourMUBWitness`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.HasLiftedFourMUBWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Three matrices each have a Hadamard-equivalent representative in the atlas and have flat transitions for every distinct pair. Compatibility is tested on the lifted matrices.

**Theorem 1.15 (Exact atlas reduction).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.nonempty_fourMUBHadamardWitness_iff_lifted_atlas`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.nonempty_fourMUBHadamardWitness_iff_lifted_atlas` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an exact atlas, a FourMUBHadamardWitness exists if and only if a lifted four-MUB witness exists over that atlas.

**Theorem 1.16 (Exclusion through an exact atlas).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.no_fourMUBHadamardWitness_of_no_lifted_atlas`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.no_fourMUBHadamardWitness_of_no_lifted_atlas` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an exact atlas has no lifted four-MUB witness, then no FourMUBHadamardWitness exists.

**Theorem 1.17 (Independent equivalence can change compatibility).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.independent_hadamard_equivalence_does_not_preserve_unbiasedness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.independent_hadamard_equivalence_does_not_preserve_unbiasedness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exist order-two complex Hadamard matrices H, K and L such that K and L are Hadamard equivalent, H and L are unbiased, and H and K are not unbiased. The witnesses are the order-two Fourier matrix and its row-phased partner.

**Definition 1.18 (Four mutually unbiased projector contexts).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.IsFourMUBContextFamily`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.IsFourMUBContextFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Four rank-one contexts in dimension six have projector overlap one-sixth for every pair of outcomes from distinct contexts.

**Theorem 1.19 (Maximal context incompatibility).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.fourMUBContexts_have_maximal_incompatibility`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.fourMUBContexts_have_maximal_incompatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every distinct pair in a four-MUB context family has normalized incompatibility equal to one.

**Theorem 1.20 (Orthogonal centered context planes).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.fourMUBContexts_have_pairwise_orthogonal_planes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.fourMUBContexts_have_pairwise_orthogonal_planes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every context in a four-MUB family is a record measurement, then distinct contexts have orthogonal centered projector planes.

**Theorem 1.21 (Aggregate commutator square).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.fourMUBContexts_have_commutator_sum_ten`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.fourMUBContexts_have_commutator_sum_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct contexts in a dimension-six four-MUB family, the sum over all pairs of outcomes of the Hilbert-Schmidt square of their projector commutator equals ten.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.ComplexSquare`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.EntrywiseUnit`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.FourMUBHadamardWitness`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.HadamardEquivalent`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.HadamardUnbiased`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.HasLiftedFourMUBWitness`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.I6`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.IsComplexHadamard`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.IsExactHadamardAtlas`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.IsFourMUBContextFamily`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.Mat6`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.fourMUBContexts_have_commutator_sum_ten`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.fourMUBContexts_have_maximal_incompatibility`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.fourMUBContexts_have_pairwise_orthogonal_planes`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.hadamardEquivalent_refl`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.hadamardEquivalent_symm`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.hadamardEquivalent_trans`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.hadamardUnbiased_symm`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.independent_hadamard_equivalence_does_not_preserve_unbiasedness`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.no_fourMUBHadamardWitness_of_no_lifted_atlas`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/MUBHadamardCompatibility.nonempty_fourMUBHadamardWitness_iff_lifted_atlas`
- Dependency: [D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes](../MutuallyUnbiasedDiagonalPlanes.md)
