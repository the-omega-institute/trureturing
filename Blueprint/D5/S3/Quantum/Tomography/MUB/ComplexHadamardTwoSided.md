# Complex Hadamard Two Sided

## Abstract

Complex Hadamards have two-sided Gram laws and scaled relative Grams.

**Theorem 1.1 (Column Gram law).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided.conjTranspose_mul_self_eq_card_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided.conjTranspose_mul_self_eq_card_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex Hadamard H on a nonempty finite coordinate type, H-adjoint times H equals the dimension times the identity.

**Theorem 1.2 (Relative Gram row law).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided.relativeGram_mul_conjTranspose_eq_card_sq_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided.relativeGram_mul_conjTranspose_eq_card_sq_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two complex Hadamards on a nonempty finite coordinate type, their relative Gram times its adjoint equals the square of the dimension times the identity.

**Theorem 1.3 (Scaled Hadamard relative Gram).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided.relativeGram_scaledHadamard`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided.relativeGram_scaledHadamard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two Hadamard-unbiased complex Hadamards on a nonempty finite coordinate type, every relative Gram entry has squared norm equal to the dimension, and its row Gram is the square of the dimension times the identity.

**Theorem 1.4 (Recovery preserves the prescribed Gram).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided.relativeGram_of_recovered_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided.relativeGram_of_recovered_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex Hadamard X on a nonempty finite coordinate type and any square complex matrix P, multiplying X times P by the inverse dimension and then multiplying on the left by X-adjoint returns P.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided.conjTranspose_mul_self_eq_card_smul`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided.relativeGram_mul_conjTranspose_eq_card_sq_smul`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided.relativeGram_of_recovered_factor`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided.relativeGram_scaledHadamard`
- Dependency: [D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing](MUBCompletionGluing.md)
