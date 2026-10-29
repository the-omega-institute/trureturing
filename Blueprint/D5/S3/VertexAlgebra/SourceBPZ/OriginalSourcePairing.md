# Original Integer-Source Bilinear Pairing

## Abstract

The literal original integer-source complex-bilinear pairing obtained by frequency retuning of the existing signed polynomial Wick supplier.

The oscillator carrier remains exactly MvPolynomial (Fin D.rank x Nat) Complex and the charge carrier remains the finite-support Finsupp carrier. integerScale k=(k+1)/(k+1/2) is nonzero and defines an algebra equivalence retune on the same polynomial ring. integerWick is the existing signed Wick form applied to retune in its first slot.

The retained bridge proves integer creation and lowering transposes, symmetry, vacuum normalization, charge isolation and both-sided nondegeneracy. The determinant-unit premise is used only by the inherited Wick nondegeneracy theorem. Rank zero and indefinite integral symmetric even Gram data remain in scope.

SourcePairingLaws proves reflection isometry, full signed energy-grade orthogonality and all integer neutral-current transposes for this form. All-source wordField BPZ induction, charged-generator transpose, fixed-grade perfection, mixed Jacobi, crossing, fusion, string consistency and AdS/CFT require further results.

**Definition 1.1 (Integer frequency retuning).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerScale`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar sends the supplier frequency k+1/2 to the required integer contraction k+1.

**Definition 1.2 (Same-ring oscillator equivalence).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.retune`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.retune` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal substitution equivalence fixes scalars and sends X(i,k) to integerScale k times X(i,k), with an actual inverse.

**Definition 1.3 (Retuned signed Wick form).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerWick`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerWick` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex-bilinear form is the existing SignedOscillatorWick.wick after retuning the first oscillator slot.

**Theorem 1.4 (Integer creation transpose).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerWick_creation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerWick_creation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by X(i,k) in the first slot transposes to -(k+1) times the actual Gram-weighted annihilation in the second slot.

**Theorem 1.5 (Integer lowering transpose).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerWick_lowering`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerWick_lowering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reverse identity is proved using the actual inverse retuning and the supplier lowering theorem.

**Theorem 1.6 (Oscillator symmetry).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerWick_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerWick_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The retuned oscillator form is symmetric by induction from its creation and lowering bridges.

**Definition 1.7 (Finite opposite-charge lift).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.sourcePairing`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.sourcePairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The form sums integerWick over the existing finite charge support and pairs charge a with charge -a.

**Theorem 1.8 (Vacuum normalization).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.sourcePairing_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.sourcePairing_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal vacuum has pairing one, including the empty-rank case.

**Theorem 1.9 (Carrier symmetry).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.sourcePairing_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.sourcePairing_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite-support induction lifts oscillator symmetry to the literal Carrier.

**Theorem 1.10 (Two-sided carrier nondegeneracy).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.sourcePairing_nondegenerate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.sourcePairing_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The opposite-charge single-sector witnesses and inherited Wick nondegeneracy prove both kernels vanish under IsUnit D.G.det.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerScale`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerWick`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerWick_creation`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerWick_lowering`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.integerWick_symmetric`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.retune`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.sourcePairing`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.sourcePairing_nondegenerate`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.sourcePairing_symmetric`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing.sourcePairing_vacuum`
- Dependency: [D5/S3/VertexAlgebra/LatticeInvolution](../LatticeInvolution.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick](../TwistedGround/SignedOscillatorWick.md)
