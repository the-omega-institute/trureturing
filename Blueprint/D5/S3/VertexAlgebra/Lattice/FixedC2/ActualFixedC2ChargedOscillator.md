# Single Oscillators on Fixed Charge Orbits

## Abstract

Actual quadratic modes reduce every single oscillator on a charged orbit.

**Theorem 1.1 (The quadratic minus-one mode on a charged ground).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator.fixed_charged_quadratic_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator.fixed_charged_quadratic_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual mode with neutral factors X(i,k) and X(j,0) on a fixed charged ground has the paired two-oscillator polynomial as its creation term. The two contractions produce single oscillators at index k+1, weighted by the corresponding Gram pairings with factors k+1 and (-1)^k.

**Theorem 1.2 (Weighted quadratic modes isolate higher oscillators).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator.fixed_higher_oscillator_mem`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator.fixed_higher_oscillator_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weight the quadratic products by the coordinates of the charge and subtract the translation of the single oscillator at index k. Translation lies in C2 and cancels the two-oscillator term. For squared norm B, the coefficient of the oscillator at index k+1 is A = (k+1)(B-1), along with a term in the charge direction. Summing again against the charge coordinates isolates that direction with coefficient A + (-1)^k B. For B ≥ 4 both coefficients are nonzero. One can recover each single oscillator in any subspace containing C2 and the weighted quadratic products.

**Definition 1.3 (Fixed states supported on a charge and its negative).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator.fixedChargeOrbit`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator.fixedChargeOrbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed charge orbit space consists of fixed states supported on the pair of charges c and -c. Neutral quadratic modes preserve this support because each constituent neutral current acts within one charge fiber.

**Theorem 1.4 (Ground charge reduction extends to all single oscillators).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator.fixed_charged_oscillator_mem_sup_orbit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator.fixed_charged_oscillator_mem_sup_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the fixed ground of squared norm at least four lies in the sum of intrinsic C2 and a target orbit space. Neutral quadratic zero modes and minus-one modes preserve that sum. The zero-mode calculation gives the first oscillator there, and the weighted minus-one calculation gives every higher single oscillator in the same sum.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator.fixedChargeOrbit`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator.fixed_charged_oscillator_mem_sup_orbit`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator.fixed_charged_quadratic_product`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOscillator.fixed_higher_oscillator_mem`
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge](ActualFixedC2GroundCharge.md)
