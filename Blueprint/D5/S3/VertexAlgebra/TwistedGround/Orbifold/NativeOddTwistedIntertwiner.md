# The Native Odd Twisted Field

## Abstract

The actual odd lattice field reverses twisted parity and satisfies finite mixed Borcherds identities.

For lattice data D with unit Gram determinant, the source is the negative eigenspace of the lattice involution. The input is the actual twisted space of parity s, and the output has parity !s.

**Definition 1.1 (The parity-changing Hahn field).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.field`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.field` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict the corrected lattice coefficients to the stated twisted parities and assemble them as a linear field with integer exponents in the doubled coordinate.

**Theorem 1.2 (Coefficients on the actual tensor).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.field_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.field_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each signed doubled exponent, the underlying tensor of the typed coefficient is the original corrected-field coefficient applied to the underlying input tensor.

**Theorem 1.3 (Vanishing at even doubled exponents).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.field_even_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.field_even_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coefficient at an even doubled exponent vanishes on both input parities.

**Definition 1.4 (The physical half-integer modes).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an integer n, take the field coefficient at doubled exponent -2n-3. This gives the bilinear operator with physical mode n+1/2.

**Theorem 1.5 (Pointwise lower truncation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each odd source and input tensor, all modes vanish for sufficiently large integer labels n.

**Theorem 1.6 (Finite mixed Borcherds identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed state a, an odd state b, a twisted input v, and integers p, q, r, the iterate uses J(p+q-i) on the odd-source product a_(r+i)b with weight binom(p,i). The first product applies the fixed mode p+r-i on the output parity to J(q+i)(b)v. The second product applies J(q+r-i)(b) after the fixed mode p+i on the input parity, with the additional sign epsilon(r). Both products carry the weight (-1)^i binom(r,i). All three families have finite support over i >= 0, and the iterate sum equals the first product sum minus the second.

**Theorem 1.7 (Translation of a physical mode).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replacing the odd source by its lattice translate changes the coefficient at label n to -(n+1/2) times the coefficient at label n-1.

**Theorem 1.8 (Iterated field differentiation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.field_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.field_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After k translations of the source, the coefficient at doubled exponent e equals the original coefficient at e+2k times the product of (e+2j)/2 for j from 1 through k.

**Theorem 1.9 (Actual output grading).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A source of lattice grade h acting at label n on an input of doubled grade M lands in doubled grade N whenever N is nonnegative and N = M+2h-2n-3.

**Theorem 1.10 (Negative output grade).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_negative_grade_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_negative_grade_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mode vanishes when the signed doubled output index M+2h-2n-3 is strictly negative.

**Theorem 1.11 (Ground return with the Gram coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_ground_return`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_ground_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On an arbitrary even ground tensor, creation in direction j at physical mode -1/2 followed by annihilation in direction i at physical mode 1/2 returns G(i,j)/2 times the input.

**Theorem 1.12 (Explicit Leech ground normalization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.leech_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.leech_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the specified weight-3/2 Leech ground vector, the mode -1/2 in direction i gives the actual nonzero one-oscillator vector of doubled grade 1. The reverse mode 1/2 in the same direction returns G(i,i)/2 times the ground vector, and the return is nonzero.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_derivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_grade`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_ground_return`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_negative_grade_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.J_truncation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.field`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.field_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.field_derivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.field_even_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner.leech_normalization`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/ActualEnergyCovariance](../../HalfFock/ActualEnergyCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualLeechHyperbolic](../../Lattice/ActualLeechHyperbolic.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldField](OriginalOrbifoldField.md)
