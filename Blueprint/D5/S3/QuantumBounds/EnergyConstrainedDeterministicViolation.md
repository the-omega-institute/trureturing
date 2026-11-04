# Deterministic violations under an energy constraint

## Abstract

Qubit channels give a strict deterministic-input violation of the separable energy bound for every positive energy budget below one half.

**Definition 1.1 (The local-channel Born functional).**

$$\forall (dp: \mathbb{N}), \forall (ds: \mathbb{N}), \forall (dm: \mathbb{N}), \forall (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(dp\right) \times \operatorname{Fin}\left(dm\right), \operatorname{Fin}\left(dp\right) \times \operatorname{Fin}\left(dm\right), \mathbb{C}\right)), \forall (lam: \operatorname{Fin}\left(2\right) \to \operatorname{MatrixMap}\left(\operatorname{Fin}\left(dp\right), \operatorname{Fin}\left(ds\right), \mathbb{C}\right)), \forall (povm: \operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(ds\right) \times \operatorname{Fin}\left(dm\right), \operatorname{Fin}\left(ds\right) \times \operatorname{Fin}\left(dm\right), \mathbb{C}\right)), \forall (b: \operatorname{Fin}\left(2\right)), \forall (x: \operatorname{Fin}\left(2\right)), \operatorname{probability}\left(sigma, lam, povm, b, x\right) = \operatorname{Complex}.\operatorname{re}\left(\operatorname{FiniteDimensional}.\operatorname{bornProbability}\left(povm\left(b\right), \operatorname{MatrixMap}.\operatorname{kron}\left(lam\left(x\right), (\operatorname{LinearMap}.\operatorname{id}: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(dm\right), \operatorname{Fin}\left(dm\right), \mathbb{C}\right)), sigma\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation.probability` (`✓ std3`).

*Citation.* Raffaele D'Avino; Gabriel Senno; Mir Alimuddin; Antonio Acín (2025). *Entanglement in the energy-constrained prepare-and-measure scenario: applications to randomness certification and channel discrimination*. URL: <https://arxiv.org/abs/2510.27559v3>.

*Commentary.*

Apply the channel selected by x to the preparation subsystem of sigma, leave the memory subsystem unchanged, and pair the resulting matrix with the effect selected by b. The value is the real part of this Born trace. The definition accepts arbitrary complex matrices and linear matrix maps; positivity and normalization are imposed in the next statement. This is the two-input, single-measurement specialization of the source's probability formula, TeX lines 137–139 and 148.

**Definition 1.2 (Strict violation at every positive energy budget).**

$$\operatorname{claim} = (\forall (\omega: \mathbb{R}), (0 < \omega) \Rightarrow ((\omega < \frac{1}{2}) \Rightarrow (\exists (dp: \mathbb{N}), \exists (ds: \mathbb{N}), \exists (dm: \mathbb{N}), \exists (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(dp\right) \times \operatorname{Fin}\left(dm\right), \operatorname{Fin}\left(dp\right) \times \operatorname{Fin}\left(dm\right), \mathbb{C}\right)), \exists (lam: \operatorname{Fin}\left(2\right) \to \operatorname{MatrixMap}\left(\operatorname{Fin}\left(dp\right), \operatorname{Fin}\left(ds\right), \mathbb{C}\right)), \exists (ham: \operatorname{Matrix}\left(\operatorname{Fin}\left(ds\right), \operatorname{Fin}\left(ds\right), \mathbb{C}\right)), \exists (g: \operatorname{Fin}\left(ds\right) \to \mathbb{C}), \exists (povm: \operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(ds\right) \times \operatorname{Fin}\left(dm\right), \operatorname{Fin}\left(ds\right) \times \operatorname{Fin}\left(dm\right), \mathbb{C}\right)), (\operatorname{Matrix}.\operatorname{PosSemidef}\left(sigma\right)) \land ((\operatorname{Matrix}.\operatorname{trace}\left(sigma\right) = 1) \land ((\forall (x: \operatorname{Fin}\left(2\right)), (\operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(lam\left(x\right)\right)) \land (\forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(dp\right), \operatorname{Fin}\left(dp\right), \mathbb{C}\right)), \operatorname{Matrix}.\operatorname{trace}\left(lam\left(x\right)\left(rho\right)\right) = \operatorname{Matrix}.\operatorname{trace}\left(rho\right))) \land ((\operatorname{Matrix}.\operatorname{IsHermitian}\left(ham\right)) \land ((\operatorname{dotProduct}\left(\operatorname{star}\left(g\right), g\right) = 1) \land ((\operatorname{Matrix}.\operatorname{mulVec}\left(ham, g\right) = 0) \land ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(ham - (1 - \operatorname{Matrix}.\operatorname{vecMulVec}\left(g, \operatorname{star}\left(g\right)\right))\right)) \land ((\forall (b: \operatorname{Fin}\left(2\right)), \operatorname{Matrix}.\operatorname{PosSemidef}\left(povm\left(b\right)\right)) \land ((povm\left(0\right) + povm\left(1\right) = 1) \land ((\forall (x: \operatorname{Fin}\left(2\right)), \operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(ham \cdot lam\left(x\right)\left(\operatorname{partialTraceRight}\left(sigma\right)\right)\right)\right) \le \omega) \land ((\operatorname{probability}\left(sigma, lam, povm, 0, 0\right) = 1) \land (\operatorname{probability}\left(sigma, lam, povm, 0, 1\right) - \operatorname{probability}\left(sigma, lam, povm, 1, 1\right) < 2 \cdot (1 - 2 \cdot \omega)^{2} - 1))))))))))))))$$

*Formalization.* `D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Raffaele D'Avino; Gabriel Senno; Mir Alimuddin; Antonio Acín (2025). *Entanglement in the energy-constrained prepare-and-measure scenario: applications to randomness certification and channel discrimination*. URL: <https://arxiv.org/abs/2510.27559v3>.

*Commentary.*

For each real energy budget strictly between zero and one half, choose finite preparation, transmitted and memory dimensions, a density matrix, two completely positive trace-preserving maps and a binary positive measurement. The Hermitian Hamiltonian annihilates a unit vector g and dominates the orthogonal complement of its rank-one projector, expressing a unique ground state at energy zero and a gap of at least one. Both prepared states satisfy the energy budget. Input zero gives outcome zero with certainty, while the input-one correlator lies strictly below the separable bound. These are the finite-dimensional conditions corresponding to the source's energy assumptions at TeX lines 151–154, correlator at 165–166, inequality at 266–270 and conjecture at 284. The statement requires the displayed state, channel and measurement conditions; it does not include a separate separability predicate.

**Theorem 1.3 (A qubit construction for the whole open interval).**

$$\forall (\omega: \mathbb{R}), (0 < \omega) \Rightarrow ((\omega < \frac{1}{2}) \Rightarrow (\exists (dp: \mathbb{N}), \exists (ds: \mathbb{N}), \exists (dm: \mathbb{N}), \exists (sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(dp\right) \times \operatorname{Fin}\left(dm\right), \operatorname{Fin}\left(dp\right) \times \operatorname{Fin}\left(dm\right), \mathbb{C}\right)), \exists (lam: \operatorname{Fin}\left(2\right) \to \operatorname{MatrixMap}\left(\operatorname{Fin}\left(dp\right), \operatorname{Fin}\left(ds\right), \mathbb{C}\right)), \exists (ham: \operatorname{Matrix}\left(\operatorname{Fin}\left(ds\right), \operatorname{Fin}\left(ds\right), \mathbb{C}\right)), \exists (g: \operatorname{Fin}\left(ds\right) \to \mathbb{C}), \exists (povm: \operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(ds\right) \times \operatorname{Fin}\left(dm\right), \operatorname{Fin}\left(ds\right) \times \operatorname{Fin}\left(dm\right), \mathbb{C}\right)), (\operatorname{Matrix}.\operatorname{PosSemidef}\left(sigma\right)) \land ((\operatorname{Matrix}.\operatorname{trace}\left(sigma\right) = 1) \land ((\forall (x: \operatorname{Fin}\left(2\right)), (\operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(lam\left(x\right)\right)) \land (\forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(dp\right), \operatorname{Fin}\left(dp\right), \mathbb{C}\right)), \operatorname{Matrix}.\operatorname{trace}\left(lam\left(x\right)\left(rho\right)\right) = \operatorname{Matrix}.\operatorname{trace}\left(rho\right))) \land ((\operatorname{Matrix}.\operatorname{IsHermitian}\left(ham\right)) \land ((\operatorname{dotProduct}\left(\operatorname{star}\left(g\right), g\right) = 1) \land ((\operatorname{Matrix}.\operatorname{mulVec}\left(ham, g\right) = 0) \land ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(ham - (1 - \operatorname{Matrix}.\operatorname{vecMulVec}\left(g, \operatorname{star}\left(g\right)\right))\right)) \land ((\forall (b: \operatorname{Fin}\left(2\right)), \operatorname{Matrix}.\operatorname{PosSemidef}\left(povm\left(b\right)\right)) \land ((povm\left(0\right) + povm\left(1\right) = 1) \land ((\forall (x: \operatorname{Fin}\left(2\right)), \operatorname{Complex}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(ham \cdot lam\left(x\right)\left(\operatorname{partialTraceRight}\left(sigma\right)\right)\right)\right) \le \omega) \land ((\operatorname{probability}\left(sigma, lam, povm, 0, 0\right) = 1) \land (\operatorname{probability}\left(sigma, lam, povm, 0, 1\right) - \operatorname{probability}\left(sigma, lam, povm, 1, 1\right) < 2 \cdot (1 - 2 \cdot \omega)^{2} - 1)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation.result` (`✓ std3`). ∎

*Resolves.* `Problems/davino-et-al-2025-energy-constrained-deterministic-violation` (proved) by `D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"davino-et-al-2025-energy-constrained-deterministic-violation","declaration_gid":"D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Raffaele D'Avino; Gabriel Senno; Mir Alimuddin; Antonio Acín (2025). *Entanglement in the energy-constrained prepare-and-measure scenario: applications to randomness certification and channel discrimination*. URL: <https://arxiv.org/abs/2510.27559v3>.

*Commentary.*

Fix 0 < ω < 1/2 and set t = (1 − 2ω)/8. Then 0 < t < 1/8. Choose the positive square roots s = √(1 − ω), r = √(ω(1/2 − t)), q = √(ω(1/2 + t)), a = √(1 − ω − 2ωt) and h = √(2ωt). Their radicands are positive, and they satisfy s² = 1 − ω, r² + q² = ω, q² − r² = h² and a² + h² = s².

Take all three systems to have dimension two. In the ordered tensor basis 00, 01, 10, 11, let ψ have coordinates (s, 0, r, q), and let σ = |ψ⟩⟨ψ|. The identity s² + r² + q² = 1 makes σ positive semidefinite with trace one and σ² = σ.

For input zero use Kraus matrices I and 0. For input one use K₀ = [[−a/s, 0], [h²/(sq), r/q]] and K₁ = [[−hr/(sq), h/q], [0, 0]]. All entries are complex embeddings of the indicated real quantities. Since s and q are nonzero, direct matrix multiplication using q² − r² = h² and a² + h² = s² gives K₀†K₀ + K₁†K₁ = I. The Kraus sums consequently define completely positive trace-preserving maps for both inputs.

Choose the Hamiltonian coordinateProjectorTwo(1), namely diag(0,1), and the ground vector evenChannelState, namely (1,0). The Hamiltonian is Hermitian, the ground vector has squared norm one, and their matrix-vector product is zero. The Hamiltonian equals I − |g⟩⟨g|, so its required positive semidefinite difference is zero. Computing the partial trace of σ and applying each Kraus sum gives the same energy r² + q² = ω for each input.

Thus the effects σ and I − σ are positive semidefinite and sum to the identity.

For the joint output, amplification by the identity applies the channel to each matrix slice with the memory indices fixed. Evaluating these slices gives σ for input zero. For input one the output is |v⟩⟨v| + h²|01⟩⟨01|, where v has coordinates (−a, 0, q, r). Taking the traces against the two effects gives p(0|0) = 1, p(0|1) = (sa − 2rq)² and p(1|1) = 1 − (sa − 2rq)². In particular, the extra |01⟩ component is orthogonal to ψ; the rank-one trace overlap is the squared modulus of their inner product.

To obtain the strict estimate, put x = sa and y = 2rq. Their squares are x² = (1 − ω)(1 − ω − 2ωt) and y² = ω²(1 − 4t²). Comparison of nonnegative squares gives x ≥ 1 − ω − 2ωt, y ≤ ω, x < 1 − ω − ωt and y ≥ ω(1 − 4t²). The first pair yields x − y ≥ (1 − 2ω)(1 − ω/4) > 0. The second pair yields x − y < 1 − 2ω − ωt(1 − 4t) < 1 − 2ω. Squaring therefore gives (sa − 2rq)² < (1 − 2ω)².

These matrices and maps satisfy every positivity, trace, ground-state, gap and energy condition in the statement. Finally, subtracting the two input-one probabilities gives 2(sa − 2rq)² − 1, which is strictly less than 2(1 − 2ω)² − 1 by the square-root estimate. The construction therefore supplies the required dimensions and objects for every energy budget in the open interval.

## References

- Truth anchor: `D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation.claim`
- Truth anchor: `D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation.probability`
- Truth anchor: `D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation.result`
- Dependency: [D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner](../Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.md)
- Dependency: [D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction](../Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence](../Quantum/QuantumChannels/IptPptSquaredEquivalence.md)
- Dependency: [D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes](../Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes.md)
