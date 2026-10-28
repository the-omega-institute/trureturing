# Volume ratios for generalized Pauli channels

## Abstract

Three volume ratios for generalized Pauli eigenvalue regions hold in every natural dimension at least two.

**Definition 1.1 (The box of positivity estimates).**

$$\forall \left(d: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.boxRegion}\left(d\right): \operatorname{Set}\left(\left(\operatorname{Fin}\left(d + 1\right)\right) \to \left(\mathbb{R}\right)\right)\right) = \{x: \left(\operatorname{Fin}\left(d + 1\right)\right) \to \left(\mathbb{R}\right) \mid \left(\forall \left(i: \operatorname{Fin}\left(d + 1\right)\right), \left(\left(\frac{-1}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right) - 1} \le x\left(i\right)\right) \land \left(x\left(i\right) \le 1\right)\right)\right)\}\right)$$

*Formalization.* `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.boxRegion` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2020). *Geometry of generalized Pauli channels*. DOI: [10.1103/PhysRevA.101.062323](https://doi.org/10.1103/PhysRevA.101.062323). URL: <https://arxiv.org/abs/2002.04657v2>.

*Commentary.*

The box consists of all real vectors x with d + 1 coordinates between −1/(d − 1) and one. It is the upper estimate for positive maps in GGPC_volume5.tex, lines 210–228; the coordinate inequalities are necessary for positivity, and are not asserted to be sufficient. The definition is a set for every natural d; its interpretation here uses d at least two.

**Definition 1.2 (The complete positivity region).**

$$\forall \left(d: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.cpRegion}\left(d\right): \operatorname{Set}\left(\left(\operatorname{Fin}\left(d + 1\right)\right) \to \left(\mathbb{R}\right)\right)\right) = \{x: \left(\operatorname{Fin}\left(d + 1\right)\right) \to \left(\mathbb{R}\right) \mid \left(\left(\frac{-1}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right) - 1} \le \sum_{i: \operatorname{Fin}\left(d + 1\right)} \left(x\left(i\right)\right)\right) \land \left(\forall \left(j: \operatorname{Fin}\left(d + 1\right)\right), \left(\sum_{i: \operatorname{Fin}\left(d + 1\right)} \left(x\left(i\right)\right) \le 1 + \left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right) \cdot x\left(j\right)\right)\right)\right)\}\right)$$

*Formalization.* `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.cpRegion` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2020). *Geometry of generalized Pauli channels*. DOI: [10.1103/PhysRevA.101.062323](https://doi.org/10.1103/PhysRevA.101.062323). URL: <https://arxiv.org/abs/2002.04657v2>.

*Commentary.*

The sum of the coordinates is at least −1/(d − 1) and at most 1 + d times each coordinate. For d at least two, the latter family of inequalities is equivalent to the upper bound 1 + d times the minimum coordinate in the generalized Fujiwara–Algoet condition of Appendix A (GGPC_volume5.tex, lines 359–364).

**Definition 1.3 (The nonnegative complete positivity region).**

$$\forall \left(d: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.generatorRegion}\left(d\right): \operatorname{Set}\left(\left(\operatorname{Fin}\left(d + 1\right)\right) \to \left(\mathbb{R}\right)\right)\right) = \operatorname{Set.inter}\left(\operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.cpRegion}\left(d\right), \{x: \left(\operatorname{Fin}\left(d + 1\right)\right) \to \left(\mathbb{R}\right) \mid \left(\forall \left(i: \operatorname{Fin}\left(d + 1\right)\right), \left(0 \le x\left(i\right)\right)\right)\}\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.generatorRegion` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2020). *Geometry of generalized Pauli channels*. DOI: [10.1103/PhysRevA.101.062323](https://doi.org/10.1103/PhysRevA.101.062323). URL: <https://arxiv.org/abs/2002.04657v2>.

*Commentary.*

Intersect the complete positivity region with the nonnegative orthant. These are the eigenvalue vectors called achievable with time-local generators in GGPC_volume5.tex, lines 256–267.

**Definition 1.4 (The entanglement-breaking region with nonnegative coordinates).**

$$\forall \left(d: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.ebRegion}\left(d\right): \operatorname{Set}\left(\left(\operatorname{Fin}\left(d + 1\right)\right) \to \left(\mathbb{R}\right)\right)\right) = \operatorname{Set.inter}\left(\operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.generatorRegion}\left(d\right), \{x: \left(\operatorname{Fin}\left(d + 1\right)\right) \to \left(\mathbb{R}\right) \mid \left(\sum_{i: \operatorname{Fin}\left(d + 1\right)} \left(x\left(i\right)\right) \le 1\right)\}\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.ebRegion` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2020). *Geometry of generalized Pauli channels*. DOI: [10.1103/PhysRevA.101.062323](https://doi.org/10.1103/PhysRevA.101.062323). URL: <https://arxiv.org/abs/2002.04657v2>.

*Commentary.*

Within the nonnegative complete positivity region, impose that the coordinate sum is at most one. This is the source's entanglement-breaking criterion for nonnegative eigenvalues (GGPC_volume5.tex, lines 282–293).

**Definition 1.5 (The weighted eigenvalue volume).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(s: \operatorname{Set}\left(\left(\operatorname{Fin}\left(d + 1\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.channelVolume}\left(d, s\right): \mathbb{R}\right) = \left(\frac{\operatorname{Real.sqrt}\left(\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right) - 1\right)}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right)}\right)^{d + 1} \cdot \operatorname{ENNReal.toReal}\left(\operatorname{MeasureTheory.volume}\left(s\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.channelVolume` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2020). *Geometry of generalized Pauli channels*. DOI: [10.1103/PhysRevA.101.062323](https://doi.org/10.1103/PhysRevA.101.062323). URL: <https://arxiv.org/abs/2002.04657v2>.

*Commentary.*

Multiply the real value of the Lebesgue measure of s by the constant (√(d − 1)/d) to the power d + 1, as in GGPC_volume5.tex, lines 222–228. The natural d is cast to a real number before subtraction, division and the square root; the exponent d + 1 remains natural. ENNReal.toReal converts the extended nonnegative measure to a real number; for d at least two, all four regions below have finite positive measure.

**Theorem 1.6 (The three ratios in every dimension at least two).**

$$\forall \left(d: \mathbb{N}\right), \left(\left(\left(2: \mathbb{N}\right) \le d\right) \to \left(\left(\frac{\operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.channelVolume}\left(d, \operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.cpRegion}\left(d\right)\right)}{\operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.channelVolume}\left(d, \operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.boxRegion}\left(d\right)\right)} = \frac{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right)}{\left(\operatorname{Nat.cast}\left(\operatorname{Nat.factorial}\left(d + 1\right)\right): \mathbb{R}\right)}\right) \land \left(\left(\frac{\operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.channelVolume}\left(d, \operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.generatorRegion}\left(d\right)\right)}{\operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.channelVolume}\left(d, \operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.cpRegion}\left(d\right)\right)} = \frac{\left(\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right)\right)^{2} - 1}{\left(\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right)\right)^{2}} \cdot \left(\frac{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right) - 1}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right)}\right)^{d}\right) \land \left(\frac{\operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.channelVolume}\left(d, \operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.ebRegion}\left(d\right)\right)}{\operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.channelVolume}\left(d, \operatorname{D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios.generatorRegion}\left(d\right)\right)} = \frac{1}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right) + 1}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.result` (`✓ std3`). ∎

*Resolves.* `Problems/siudzinska-2020-generalized-pauli-volume-ratios` (proved) by `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"siudzinska-2020-generalized-pauli-volume-ratios","declaration_gid":"D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Katarzyna Siudzińska (2020). *Geometry of generalized Pauli channels*. DOI: [10.1103/PhysRevA.101.062323](https://doi.org/10.1103/PhysRevA.101.062323). URL: <https://arxiv.org/abs/2002.04657v2>.

*Commentary.*

The three identities are the conjectures in GGPC_volume5.tex, lines 243–246, 276–279 and 302–305. They concern the four specified subsets of real coordinate space for every natural d at least two. They do not require the existence of d + 1 mutually unbiased bases in each such dimension.

Fix d at least two, put m = d + 1, and let S be the standard simplex of nonnegative m-coordinate vectors whose coordinate sum is at most one. Its Lebesgue measure is 1/m!. Write u for the vector of ones. For a positive real c, consider the affine image T_c(S), where T_c(t) = u + c(t − (∑ⱼ tⱼ)u). The linear part has matrix c(I − J), with J the matrix of ones. Factor J as the product of an m-by-one column of ones and a one-by-m row of ones. The identity det(I − AB) = det(I − BA) reduces det(I − J) to the one-by-one determinant 1 − m = −d. Thus the absolute determinant of the linear part is d cᵐ. Translation invariance and the determinant formula for the image of Lebesgue measure give measure d cᵐ/m! for T_c(S).

The coordinate sum of T_c(t) is m − cd∑ⱼ tⱼ. Consequently T_c(S) consists exactly of the vectors x with m − cd ≤ s and s ≤ 1 + d xⱼ for every j, where s = ∑ᵢ xᵢ. For the converse, set tᵢ = (d xᵢ − s + 1)/(cd). The upper inequalities make each tᵢ nonnegative, and ∑ᵢ tᵢ = (m − s)/(cd) is at most one by the lower inequality. Substituting these coordinates gives T_c(t) = x. Now put L = d/(d − 1). Since m − Ld = −1/(d − 1), the complete positivity region is T_L(S), and its measure is d Lᵐ/m!.

The nonnegative complete positivity region is S ∪ T_1(S). Indeed, a vector in that region with coordinate sum at most one lies in S; if its sum is greater than one, the preceding characterization puts it in T_1(S). Conversely, nonnegativity and a sum at most one imply the complete positivity inequalities for every vector in S. For a vector in T_1(S), the sum is at least one, and its upper inequalities then force every coordinate to be nonnegative. The two simplices intersect only where the coordinate sum equals one. This hyperplane has zero Lebesgue measure. The set S is measurable as the intersection of its coordinate halfspaces and its sum halfspace, so the union has measure 1/m! + d/m! = (d + 1)/m!.

The entanglement-breaking region is exactly S: membership gives nonnegative coordinates and a sum at most one, while these two conditions already imply complete positivity. Its measure is therefore 1/m!. The box is the closed coordinate interval with constant endpoints −1/(d − 1) and one. Each side has length L, and the product formula for the measure of a box gives its measure Lᵐ.

All four measures are finite and positive because d, d − 1, L and m! are positive. The common weight (√(d − 1)/d)ᵐ is also positive, so it cancels from every quotient. The first quotient is (d Lᵐ/m!)/Lᵐ = d/m!. The second is ((d + 1)/m!)/(d Lᵐ/m!) = (d + 1)/(d Lᵐ); expanding m = d + 1 and L = d/(d − 1) gives ((d² − 1)/d²)((d − 1)/d)ᵈ. The last quotient is (1/m!)/((d + 1)/m!) = 1/(d + 1).

## References

- Truth anchor: `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.boxRegion`
- Truth anchor: `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.channelVolume`
- Truth anchor: `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.cpRegion`
- Truth anchor: `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.ebRegion`
- Truth anchor: `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.generatorRegion`
- Truth anchor: `D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios.result`
- Dependency: [D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound](../Quantum/Measurement/ConditionalSubentropyGuessingBound.md)
