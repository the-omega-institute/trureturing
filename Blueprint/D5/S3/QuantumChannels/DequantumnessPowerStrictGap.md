# A strict gap between two dequantumness powers

## Abstract

A translated qubit contraction has strictly greater unrestricted two-state dequantumness power than its restriction to maximally quantum inputs.

**Definition 1.1 (Quantumness of two weighted matrices).**

$$\forall \left(p: \mathbb{R}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\forall \left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.quantumness}\left(p, \rho, \sigma\right): \mathbb{R}\right) = -\left(\sum_{i: \operatorname{Fin}\left(2\right)} \left(\sum_{j: \operatorname{Fin}\left(2\right)} \left(\left(![p, \left(1: \mathbb{R}\right) - p]\left(i\right) \cdot ![p, \left(1: \mathbb{R}\right) - p]\left(j\right)\right) \cdot \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\left(![\rho, \sigma]\left(i\right) \cdot ![\rho, \sigma]\left(j\right) - ![\rho, \sigma]\left(j\right) \cdot ![\rho, \sigma]\left(i\right)\right)^{\left(2: \mathbb{N}\right)}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.quantumness` (`✓ std3`).

*Citation.* Hongting Song; Nan Li (2022). *Quantumness and Dequantumness Power of Quantum Channels*. DOI: [10.3390/e24081146](https://doi.org/10.3390/e24081146). URL: <https://europepmc.org/article/PMC/PMC9407519>.

*Commentary.*

Equation (1) of Song and Li, Section 2, measures ensemble quantumness by the negative weighted sum of traces of squared commutators. Here the weights are p and 1-p and the matrices are ρ and σ. Matrix products and squares are over the complex numbers, and Complex.re takes the real part after the trace. The expression is defined for every real p and every pair of complex two-by-two matrices; density and probability conditions enter through IsEnsemble below.

**Definition 1.2 (Unrestricted two-state dequantumness power).**

$$\forall \left(\varphi: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.dequantumnessPower}\left(\varphi\right): \mathbb{R}\right) = \operatorname{sSup}\left(\{\left(x: \mathbb{R}\right) \mid \exists \left(p: \mathbb{R}\right), \left(\exists \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\exists \left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.AdaptiveQueryQubitFourStateRefutation.IsEnsemble}\left(![p, \left(1: \mathbb{R}\right) - p], ![\rho, \sigma]\right)\right) \land \left(x = \operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.quantumness}\left(p, \rho, \sigma\right) - \operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.quantumness}\left(p, \varphi\left(\rho\right), \varphi\left(\sigma\right)\right)\right)\right)\right)\right)\}\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.dequantumnessPower` (`✓ std3`).

*Citation.* Hongting Song; Nan Li (2022). *Quantumness and Dequantumness Power of Quantum Channels*. DOI: [10.3390/e24081146](https://doi.org/10.3390/e24081146). URL: <https://europepmc.org/article/PMC/PMC9407519>.

*Commentary.*

This is D₂ from the definition of D in Section 3: take the real supremum of the decrease of quantumness over all two-state qubit ensembles. IsEnsemble requires nonnegative weights summing to one and positive semidefinite matrices of trace one, equivalently 0 ≤ p ≤ 1 with both ρ and σ density matrices. MatrixMap denotes a complex-linear map on the matrix space. This definition accepts every such map; complete positivity and trace preservation are imposed in the equality question.

**Definition 1.3 (Maximal initial two-state quantumness).**

$$\left(\operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.maxQuantumness}: \mathbb{R}\right) = \operatorname{sSup}\left(\{\left(x: \mathbb{R}\right) \mid \exists \left(p: \mathbb{R}\right), \left(\exists \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\exists \left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.AdaptiveQueryQubitFourStateRefutation.IsEnsemble}\left(![p, \left(1: \mathbb{R}\right) - p], ![\rho, \sigma]\right)\right) \land \left(x = \operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.quantumness}\left(p, \rho, \sigma\right)\right)\right)\right)\right)\}\right)$$

*Formalization.* `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.maxQuantumness` (`✓ std3`).

*Citation.* Hongting Song; Nan Li (2022). *Quantumness and Dequantumness Power of Quantum Channels*. DOI: [10.3390/e24081146](https://doi.org/10.3390/e24081146). URL: <https://europepmc.org/article/PMC/PMC9407519>.

*Commentary.*

The maximal initial quantumness is the real supremum over all two-state qubit ensembles. This specializes the maximal-quantumness condition in the definition of D' in Section 3 to two ingredients. Its value is one quarter, attained by equal weights and orthogonal unit Bloch vectors.

**Definition 1.4 (Dequantumness power on maximally quantum inputs).**

$$\forall \left(\varphi: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.restrictedDequantumnessPower}\left(\varphi\right): \mathbb{R}\right) = \operatorname{sSup}\left(\{\left(x: \mathbb{R}\right) \mid \exists \left(p: \mathbb{R}\right), \left(\exists \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\exists \left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.AdaptiveQueryQubitFourStateRefutation.IsEnsemble}\left(![p, \left(1: \mathbb{R}\right) - p], ![\rho, \sigma]\right)\right) \land \left(\left(\operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.quantumness}\left(p, \rho, \sigma\right) = \operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.maxQuantumness}\right) \land \left(x = \operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.quantumness}\left(p, \rho, \sigma\right) - \operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.quantumness}\left(p, \varphi\left(\rho\right), \varphi\left(\sigma\right)\right)\right)\right)\right)\right)\right)\}\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.restrictedDequantumnessPower` (`✓ std3`).

*Citation.* Hongting Song; Nan Li (2022). *Quantumness and Dequantumness Power of Quantum Channels*. DOI: [10.3390/e24081146](https://doi.org/10.3390/e24081146). URL: <https://europepmc.org/article/PMC/PMC9407519>.

*Commentary.*

This is the two-state restriction D₂′ from the definition of D' in Section 3. The same loss is optimized only over input ensembles whose quantumness equals maxQuantumness. Both the ensemble condition and the equality to that supremum are required. The supremum is taken in the real numbers.

**Definition 1.5 (Universal equality for qubit channels).**

$$\left(\operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.claim}: \operatorname{Prop}\right) = \left(\forall \left(\varphi: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsCPTP}\left(\varphi\right)\right) \to \left(\operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.dequantumnessPower}\left(\varphi\right) = \operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.restrictedDequantumnessPower}\left(\varphi\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hongting Song; Nan Li (2022). *Quantumness and Dequantumness Power of Quantum Channels*. DOI: [10.3390/e24081146](https://doi.org/10.3390/e24081146). URL: <https://europepmc.org/article/PMC/PMC9407519>.

*Commentary.*

The assertion is that every completely positive trace-preserving complex-linear qubit map has equal unrestricted and restricted two-state dequantumness powers. In the conjecture at the end of Section 3, Song and Li state that this equality can fail and ask for a strict separation. Thus negating the displayed universal equality establishes the failure they seek.

**Theorem 1.6 (A qubit map with a strict gap).**

$$\neg \left(\operatorname{D5.S3.QuantumChannels.DequantumnessPowerStrictGap.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.result` (`✓ std3`). ∎

*Resolves.* `Problems/song-li-2022-dequantumness-power-strict-gap` (refuted) by `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"song-li-2022-dequantumness-power-strict-gap","declaration_gid":"D5/S3/QuantumChannels/DequantumnessPowerStrictGap.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hongting Song; Nan Li (2022). *Quantumness and Dequantumness Power of Quantum Channels*. DOI: [10.3390/e24081146](https://doi.org/10.3390/e24081146). URL: <https://europepmc.org/article/PMC/PMC9407519>.

*Commentary.*

For two weights p and 1-p, the ensemble condition is precisely 0 ≤ p ≤ 1 together with positive semidefiniteness and unit trace of ρ and σ. Consider the map φ(X) = X/2 + tr(X) diag(3/4,1/4)/2. On Bloch vectors it will act by the translated contraction f(r) = r/2 + e_z/4, where e_z = (0,0,1).

First take orthonormal real three-vectors r and s, and put w = r × s. Then w has squared norm one, and (f(r) × f(s)) · w = 1/4 + (r₂+s₂)/8. Cauchy-Schwarz applied to r+s and e_z gives (r₂+s₂)² ≤ 2, hence r₂+s₂ ≥ −√2. The projection is therefore at least 1/4−√2/8, which is positive because √2 < 2. Applying Cauchy-Schwarz again, now to f(r) × f(s) and w, yields ‖f(r) × f(s)‖² ≥ (1/4)(1/2−√2/4)².

Every qubit density matrix has the form B(r) = (I+r₀σₓ+r₁σᵧ+r₂σ_z)/2 for a real Bloch vector r of norm at most one, where σₓ, σᵧ and σ_z are the Pauli matrices. The Bloch commutator Gram identity gives Q = p(1-p)‖r × s‖². Lagrange's identity shows 0 ≤ ‖r × s‖² ≤ 1 whenever r and s lie in the unit ball. A Hermitian idempotent of trace one is a density matrix. Since 0 ≤ p(1-p) ≤ 1/4, every valid two-state ensemble satisfies 0 ≤ Q ≤ 1/4.

Equal weights with ρ = diag(1,0) and σ = (1/2)[[1,1],[1,1]] attain Q = 1/4; these matrices are Hermitian idempotents of trace one. The quantumness values form a nonempty set bounded above by 1/4, so their supremum is exactly 1/4. If an ensemble attains it, saturation of p(1-p)‖r × s‖² ≤ 1/4 forces p = 1/2 and ‖r × s‖² = 1. Using ‖r × s‖² = (r·r)(s·s)−(r·s)² with each squared norm at most one then forces r·r = s·s = 1 and r·s = 0.

Direct substitution in the Bloch matrix gives φ(B(r)) = B(f(r)). Complete positivity follows from five complex Kraus matrices: (√2/2)I, diag(√6/4,0), (√6/4)E₀₁, (√2/4)E₁₀ and (√2/4)E₁₁. Here Eᵢⱼ has its only nonzero entry, equal to one, at row i and column j, with zero-based indices. Their Kraus sum is φ. Also tr(φ(X)) = tr(X)/2 + tr(X)(3/4+1/4)/2 = tr(X), so φ is trace preserving.

Next put q = √145 and take p = 1/2, ρ = (1/34)[[5,q],[q,29]] and σ = (1/34)[[5,−q],[−q,29]]. The identity q² = 145 shows that both matrices are Hermitian idempotents of trace one. They therefore form a valid ensemble, and direct expansion of its quantumness loss under φ gives L = 1329215/5345344.

For any ensemble with maximal initial quantumness, the preceding characterization supplies equal weights and orthonormal unit Bloch vectors. The bound for the translated cross product then gives Q(input)−Q(output) ≤ U, where U = (29+2√2)/128.

All unrestricted losses are bounded above by 1/4: input quantumness is at most 1/4, and output quantumness is nonnegative by its Bloch expression. The explicit ensemble contributes L to this bounded set, hence L ≤ dequantumnessPower(φ). The restricted loss set is nonempty because an ensemble attaining maximal quantumness exists; every member is at most U, so restrictedDequantumnessPower(φ) ≤ U.

Finally √2 is nonnegative, its square is two, and rational comparison of squares gives √2 < 236321/167042. It follows that U < L. If the universal equality held, applying it to the completely positive trace-preserving map φ would identify the two suprema, contradicting L ≤ dequantumnessPower(φ) = restrictedDequantumnessPower(φ) ≤ U < L. Thus this map has strictly greater unrestricted two-state dequantumness power.

## References

- Truth anchor: `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.claim`
- Truth anchor: `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.dequantumnessPower`
- Truth anchor: `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.maxQuantumness`
- Truth anchor: `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.quantumness`
- Truth anchor: `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.restrictedDequantumnessPower`
- Truth anchor: `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.result`
- Dependency: [D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex](../Combinatorics/Orthogonality/ThetaRepresentationNonconvex.md)
- Dependency: [D5/S3/Quantum/CommutingMidpoint](../Quantum/CommutingMidpoint.md)
- Dependency: [D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation](../Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.md)
- Dependency: [D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity](PurelyNonUnitalEternalNonMarkovianity.md)
