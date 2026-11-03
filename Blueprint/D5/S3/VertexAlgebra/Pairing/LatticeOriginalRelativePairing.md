# Original relative tensor pairing

## Abstract

Original all-charge relative tensor pairing with arbitrary complex transverse basis and signed-degree selection.

The construction uses the canonical OriginalMatterHermitian Hm, the original signed ghost form, and literal c0 insertion on the all-integral-charge Carrier tensor occupation Fock. Reality is assumed only for the two longitudinal null vectors; the transverse basis is an arbitrary complex basis of their actual orthogonal complement.

The public theorem escape audit remains unfinished. Issue https://github.com/the-omega-institute/trureturing/issues/25857 records the missing realization, exact reconstruction, lawful template, whole-family variation, sensitivity, and observational-dependence evidence. This issue is the documented audit exception and is not a validated registration. The full BRST/HPL/no-ghost and string programme remains outside this unit.

**Theorem 1.1 (Canonical matter sesquilinear form).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.matterForm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.matterForm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matter form is the canonical frame-free Hm.

**Theorem 1.2 (Charge-diagonal matter pairing).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.Hm_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.Hm_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Single-charge states pair through integerWick with the original signed oscillator conjugation.

**Theorem 1.3 (Ground-state charge pairing).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.Hm_ground`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.Hm_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integral momentum, including zero, has the same unit ground norm on the matching charge.

**Theorem 1.4 (Conjugation on the transverse complement).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.conjugateK`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.conjugateK` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjugated transverse vector remains in the actual orthogonal complement under the two longitudinal reality hypotheses.

**Theorem 1.5 (Arbitrary complex-basis conjugation transport).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.conjugateK_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.conjugateK_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation is expanded in the supplied complex transverse basis without imposing reality or orthonormality on that basis.

**Theorem 1.6 (Complete-basis directions).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.direction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.direction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete basis consists of the two longitudinal directions and the supplied transverse basis.

**Theorem 1.7 (Inverse coordinate equivalence).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.phi`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial coordinates are transported to the original oscillator algebra by the inverse coordinate equivalence.

**Theorem 1.8 (Transverse conjugation transport).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.kappa_phi_transverse`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.kappa_phi_transverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjugate of a transverse generator is the finite complex basis combination obtained from conjugateK.

**Theorem 1.9 (Generator conjugation transport).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.kappa_phi_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.kappa_phi_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original oscillator conjugation is transported on every complete-basis generator.

**Theorem 1.10 (Original annihilation derivation).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.originalDerivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.originalDerivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative is the original Gram-weighted annihilation derivation.

**Theorem 1.11 (Complete-basis coordinate derivation).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.coordinateDerivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.coordinateDerivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate derivation uses the actual Gram pairings against the complete basis.

**Theorem 1.12 (Derivative transport).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.derivative_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.derivative_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original derivative and the complete-basis coordinate derivative are intertwined by the inverse coordinate equivalence.

**Theorem 1.13 (Creation-contraction recursion).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.integerWick_lin_creation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.integerWick_lin_creation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A creation polynomial contracts against integerWick through the original derivative with the signed frequency factor.

**Theorem 1.14 (Original oscillator form).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillatorForm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillatorForm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The oscillator form retains the original conjugation and signed Wick form.

**Theorem 1.15 (Oscillator creation recursion).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_creation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_creation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Creation in the first argument is transferred to the original coordinate contraction in the second argument.

**Theorem 1.16 (One-particle Gram contraction).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_X_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_X_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Same-frequency generators pair by the original Gram form, with the signed frequency weight.

**Theorem 1.17 (Signed Gram selection).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.gram_weight_selection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.gram_weight_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Opposite longitudinal signed weights are required for a nonzero complete-basis Gram coefficient.

**Theorem 1.18 (Contraction support degree).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.contraction_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.contraction_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero contraction coefficient has the degree forced by the derivative variable weight.

**Theorem 1.19 (Oscillator signed-degree selection).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_monomial_selection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_monomial_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Wick induction proves vanishing for every monomial pair whose signed degrees do not sum to zero.

**Theorem 1.20 (Matter basis selection).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.matter_basis_selection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.matter_basis_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical matter form vanishes on charge-matched basis monomials with non-opposite oscillator degrees.

**Theorem 1.21 (Signed ghost form).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.ghostForm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.ghostForm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ghost form is the canonical signed Hermitian form on the occupation Fock.

**Theorem 1.22 (Signed ghost c0 coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.ghost_relative_signed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.ghost_relative_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal c0 insertion retains both the row sign and Jordan-Wigner phase.

**Theorem 1.23 (Ghost charge selection).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.ghost_relative_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.ghost_relative_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero signed ghost coefficient with c0 forces total ghost charge two.

**Theorem 1.24 (Original tensor form).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.totalForm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.totalForm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tensor universal property combines the canonical matter and signed ghost forms.

**Theorem 1.25 (Tensor generator formula).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.totalForm_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.totalForm_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On pure tensors the total form is the product of the canonical matter and ghost pairings.

**Theorem 1.26 (Relative c0 form).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.relativeForm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.relativeForm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relative form inserts c0 on the original ghost tensor factor.

**Theorem 1.27 (Relative tensor formula).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.relativeForm_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.relativeForm_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On pure tensors the relative form is Hm times the signed ghost c0 coefficient.

**Theorem 1.28 (Actual basis formula).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.relativeForm_actualBasis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.relativeForm_actualBasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relative form on the actual basis separates charge, oscillator, and ghost factors.

**Theorem 1.29 (Opposite-degree basis orthogonality).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.actual_opposite_degree`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.actual_opposite_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original basis pairing vanishes whenever the complete state degrees do not sum to zero.

**Theorem 1.30 (Finite support orthogonality).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.actual_support_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.actual_support_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite support separation by signed degree implies orthogonality for arbitrary carrier states.

**Theorem 1.31 (Matter form identity).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.matterForm_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.matterForm_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The linear-form wrapper evaluates to the canonical Hm.

**Theorem 1.32 (Coordinate generator identity).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.phi_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.phi_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse coordinate equivalence sends each polynomial generator to its complete-basis oscillator generator.

**Theorem 1.33 (Derivative expansion).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.originalDerivative_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.originalDerivative_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original derivative expands as the finite Gram-weighted annihilation sum.

**Theorem 1.34 (Coordinate derivative expansion).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.coordinateDerivative_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.coordinateDerivative_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete-basis coordinate derivative expands as the finite Gram-weighted partial-derivative sum.

**Theorem 1.35 (Derivative on linear generators).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.originalDerivative_lin`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.originalDerivative_lin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original derivative on a linear generator is the same-frequency Gram coefficient.

**Theorem 1.36 (Vacuum coefficient extraction).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_one_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_one_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The oscillator form with the unit first argument extracts the constant coefficient.

**Theorem 1.37 (Finite right expansion).**

Lean statement: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_right_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_right_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The oscillator form expands over the finite polynomial support of its right argument.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.Hm_ground`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.Hm_single`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.actual_opposite_degree`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.actual_support_orthogonal`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.conjugateK`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.conjugateK_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.contraction_support`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.coordinateDerivative`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.coordinateDerivative_apply`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.derivative_transport`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.direction`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.ghostForm`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.ghost_relative_nonzero`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.ghost_relative_signed`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.gram_weight_selection`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.integerWick_lin_creation`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.kappa_phi_X`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.kappa_phi_transverse`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.matterForm`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.matterForm_apply`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.matter_basis_selection`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.originalDerivative`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.originalDerivative_apply`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.originalDerivative_lin`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillatorForm`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_X_X`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_creation`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_monomial_selection`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_one_left`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.oscillator_right_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.phi`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.phi_X`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.relativeForm`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.relativeForm_actualBasis`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.relativeForm_tmul`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.totalForm`
- Truth anchor: `D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing.totalForm_tmul`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostHermitian](../../Quantum/Fermionic/BcGhostHermitian.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration](../Lattice/LatticeBRSTModeFiltration.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame](../Lattice/LatticeRealNullFrame.md)
- Dependency: [D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing](FiniteDegreePairing.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian](../SourceBPZ/OriginalMatterHermitian.md)
