# Concentration for a finite Hermitian sign matrix

## Abstract

Sub-Gaussian tails for finite Hermitian sign matrices.

**Definition 1.1 (Uniform measure on the sign cube).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMeasure`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The probability space is the set of all Boolean assignments to the sign coordinates, with uniform measure.

**Theorem 1.2 (Fixed-vector quadratic tail).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_quadratic_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_quadratic_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A quadratic form at a vector of Euclidean norm at most one is a real linear form in independent signed variables. Its squared coefficient norm is bounded by 18/25. The two one-sided sub-Gaussian bounds give the absolute tail.

**Definition 1.3 (Sign value).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signValue`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read true as plus one and false as minus one.

**Definition 1.4 (Sign cube measure is probability measure).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMeasure_isProbabilityMeasure`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMeasure_isProbabilityMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The uniform measure on all Boolean assignments to a finite coordinate set has total mass one.

**Theorem 1.5 (Sign cube measure eq pi).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMeasure_eq_pi`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMeasure_eq_pi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform measure is the product of the uniform measures on each Boolean coordinate.

**Definition 1.6 (Sign linear form).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signLinearForm`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signLinearForm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate the sum over all coordinates of the signed real coefficient at that coordinate.

**Theorem 1.7 (Sign linear form has subgaussian mgf).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signLinearForm_hasSubgaussianMGF`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signLinearForm_hasSubgaussianMGF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The moment-generating function of the signed linear form is bounded by the sub-Gaussian bound with variance proxy the sum of squared coefficients.

**Definition 1.8 (Hermitian sign index).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.HermitianSignIndex`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.HermitianSignIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinates consist of a Boolean component selector and an ordered pair of matrix indices.

**Definition 1.9 (Sign cube matrix).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMatrix`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the Boolean-selected coordinates for the real and imaginary signs in the finite sign matrix.

**Definition 1.10 (Sign cube sample).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the product of two copies of Fin d, read the two signs per index pair from one assignment in the cube.

**Definition 1.11 (Sign component).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signComponent`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signComponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Return the imaginary part when the Boolean selector is true and the real part otherwise.

**Definition 1.12 (Sign bilinear coefficients).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signBilinearCoefficients`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signBilinearCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each component of the bilinear form, combine the two terms attached to an upper entry and its conjugate into real coefficients of the two sign bits. Inactive coordinates carry zero coefficient.

**Theorem 1.13 (Sign cube matrix bilinear component eq).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMatrix_bilinear_component_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMatrix_bilinear_component_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each chosen real or imaginary component of the bilinear form is the signed linear form in its specified coefficients.

**Theorem 1.14 (Sign bilinear coefficients energy le).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signBilinearCoefficients_energy_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signBilinearCoefficients_energy_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of squared real coefficients is at most eighteen twenty-fifths times the product of the squared Euclidean norms of the two vectors.

**Theorem 1.15 (Sign cube sample bilinear component has subgaussian mgf).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_bilinear_component_hasSubgaussianMGF`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_bilinear_component_hasSubgaussianMGF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For vectors of Euclidean norm at most one the selected component has sub-Gaussian variance proxy eighteen twenty-fifths.

**Theorem 1.16 (Sign cube sample bilinear component tail).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_bilinear_component_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_bilinear_component_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unit-ball input vectors and nonnegative threshold, the signed-component absolute tail uses variance proxy eighteen twenty-fifths.

**Theorem 1.17 (Sign cube sample bilinear tail).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_bilinear_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_bilinear_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Control the absolute complex bilinear form by the union of the real and imaginary component tails at threshold divided by the square root of two.

**Theorem 1.18 (Sign cube sample bilinear finset tail).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_bilinear_finset_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_bilinear_finset_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite family of pairs of unit-ball vectors has a simultaneous upper tail bounded by the sum of their individual bilinear bounds.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.HermitianSignIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signBilinearCoefficients`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signBilinearCoefficients_energy_le`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signComponent`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMatrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMatrix_bilinear_component_eq`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMeasure`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMeasure_eq_pi`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMeasure_isProbabilityMeasure`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_bilinear_component_hasSubgaussianMGF`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_bilinear_component_tail`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_bilinear_finset_tail`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_bilinear_tail`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_quadratic_tail`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signLinearForm`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signLinearForm_hasSubgaussianMGF`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signValue`
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices](FiniteSignMatrices.md)
