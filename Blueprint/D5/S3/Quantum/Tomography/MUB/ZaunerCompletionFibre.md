# Zauner Completion Fibre

## Abstract

Structural zeros obstruct nonzero flat moduli for Zauner relative Grams.

**Definition 1.1 (Unnormalized Zauner left factor).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor`

*Formalization.* `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex square matrix F and row weights x, the matrix on Fin 2 times the coordinate type has blocks F, xF, F, and minus xF, where xF multiplies each row of F by its weight.

**Theorem 1.2 (Upper-right cross block vanishes).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor_crossGram_upperRight_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor_crossGram_upperRight_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite Fourier coordinate type, any common block F, and any two row-weight families, the upper-right block of the adjoint of the first Zauner left factor times the second is zero.

**Theorem 1.3 (Lower-left cross block vanishes).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor_crossGram_lowerLeft_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor_crossGram_lowerLeft_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite Fourier coordinate type, any common block F, and any two row-weight families, the lower-left block of the adjoint of the first Zauner left factor times the second is zero.

**Theorem 1.4 (Factor-relative flatness obstruction).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor_crossGram_not_nonzero_flat`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor_crossGram_not_nonzero_flat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty finite coordinate type, the relative Gram of two Zauner left factors with the same block F cannot have every entry of squared norm equal to a prescribed nonzero real number.

**Theorem 1.5 (Distinct completion modes decouple).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor_mul_conjTranspose_offMode_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor_mul_conjTranspose_offMode_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If F times its adjoint is the identity, the first Zauner left factor times the adjoint of a second with the same F has zero entries between distinct Fourier coordinates, for either choice of block rows and arbitrary row-weight families.

**Theorem 1.6 (Canonical completion flatness obstruction).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerCanonicalCompletion_crossGram_not_nonzero_flat`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerCanonicalCompletion_crossGram_not_nonzero_flat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a three-by-three F with row Gram equal to the identity and any two row-weight families, the first Zauner left factor times the adjoint of the second cannot have every entry of squared norm equal to a prescribed nonzero real number.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerCanonicalCompletion_crossGram_not_nonzero_flat`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor_crossGram_lowerLeft_zero`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor_crossGram_not_nonzero_flat`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor_crossGram_upperRight_zero`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre.zaunerLeftFactor_mul_conjTranspose_offMode_zero`
- Dependency: [D5/S3/Quantum/Tomography/MUB/MUBCubeCompatibility](MUBCubeCompatibility.md)
