# Finite Spans for Charged Ground States and Single Oscillators

## Abstract

A finite-dimensional module over the neutral image contains all charged single-oscillator classes.

**Definition 1.1 (The span of neutral multiples of the ground and first oscillators).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite.leechChargedSingleSpan`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite.leechChargedSingleSpan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a fixed charge c, use the ground class and the first oscillator class in each Leech basis direction as generators. For each generator take the image of the neutral subspace under multiplication by that generator. Their sum is the indicated charged submodule.

**Theorem 1.2 (The charged span is finite-dimensional).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite.leech_charged_single_span_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite.leech_charged_single_span_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The neutral image is finite-dimensional over the complex numbers. Its image under multiplication by any generator is finite-dimensional, and the sum is indexed by the ground and the finitely many basis directions.

**Theorem 1.3 (Neutral multiplication preserves the charged span).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite.leech_charged_single_span_mul_mem`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite.leech_charged_single_span_mul_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The neutral image is a subalgebra containing the unit. The unit puts each generator in its own summand, and associativity absorbs a neutral multiplier into the neutral factor of each product. This gives stability under the actual neutral (-1)-mode on representatives.

**Theorem 1.4 (All single oscillators on a nonzero charge belong to the span).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite.leech_charged_oscillator_class_mem`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite.leech_charged_oscillator_class_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero Leech charge has squared norm at least four. Each weighted quadratic mode on its ground state comes from multiplication by a neutral class and thus lies in the charged span after taking the quotient. The single-oscillator isolation applies in the inverse image of this span, which contains intrinsic C2. The first oscillators are already generators.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite.leechChargedSingleSpan`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite.leech_charged_oscillator_class_mem`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite.leech_charged_single_span_finite`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite.leech_charged_single_span_mul_mem`
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator](ActualFixedC2ChargedOscillator.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralFinite](ActualFixedC2NeutralFinite.md)
