# SourceGeneration

## Abstract

SourceGeneration

The source is the original finitely supported charge family of oscillator polynomials. No charge generating set or positive definite form is assumed. A negative neutral mode with index -(n+1) multiplies the polynomial in its charge sector by X(i,n). Thus a monomial is produced by its occurrence word on the same charged ground.

Theta reverses the charge and negates every oscillator. The projection is one half times b plus its signed reflection. Projection across each negative current reverses the selected ground sign; the explicit finite expansion keeps the original charge support and each polynomial support independent.

The construction permits rank zero, zero charges and a vanishing minus sector. It uses no division by a charge and makes no finite-dimensionality claim. These are repository-derived consequences of the native source formulas and classical lattice involution calculus; no literature novelty or physical realization is asserted.

**Theorem 1.1 (Opposite source signs).**

Lean statement: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.sectorSign_not`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.sectorSign_not` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Negating the Bool sector negates its complex eigenvalue.

**Theorem 1.2 (Involutive source sign).**

Lean statement: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.sectorSign_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.sectorSign_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of the two eigenvalues has square one, including when the associated eigenspace vanishes.

**Theorem 1.3 (Word parity and sign reversal).**

Lean statement: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.wordParity_not`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.wordParity_not` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite word commutes with reversing its input sector.

**Theorem 1.4 (Finite theta eigensource expansion).**

Lean statement: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.theta_source_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.theta_source_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual source b and either sector, the projection is the double finite sum over b.support and each independent polynomial support. Its coefficient is the original oscillator coefficient, and its summand is the actual rightCurrentWord on a projected charged ground with the sign reversed once per letter.

**Theorem 1.5 (Actual projection eigenvalue).**

Lean statement: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.sectorProject_eigen`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.sectorProject_eigen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theta projection has the selected eigenvalue on the original carrier, including its zero component.

**Theorem 1.6 (Charged ground eigenvalue).**

Lean statement: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.projectedGround_eigen`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.projectedGround_eigen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projected charge ground has the declared theta sign for every charge, including zero.

**Theorem 1.7 (Current-word eigenvalue).**

Lean statement: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.rightCurrentWord_eigen`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.rightCurrentWord_eigen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each actual negative neutral current reverses the theta eigenvalue. The word has sector wordParity(word,epsilon).

## References

- Truth anchor: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.projectedGround_eigen`
- Truth anchor: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.rightCurrentWord_eigen`
- Truth anchor: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.sectorProject_eigen`
- Truth anchor: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.sectorSign_not`
- Truth anchor: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.sectorSign_square`
- Truth anchor: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.theta_source_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceGeneration.wordParity_not`
- Dependency: [D5/S3/VertexAlgebra/GroundRightCurrentTransport/Propagation](Propagation.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeInvolution](../LatticeInvolution.md)
