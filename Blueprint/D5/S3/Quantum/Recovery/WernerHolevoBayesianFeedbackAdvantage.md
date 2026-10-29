# Bayesian feedback advantage for the qutrit Werner–Holevo channel

## Abstract

Bayesian feedback exceeds every two-step Markovian fidelity for the qutrit Werner–Holevo channel.

**Definition 1.1 (Finite Kraus decompositions of the Werner–Holevo channel).**

$$\forall (m: \mathbb{N}), (\forall (k: (\operatorname{Fin}\left(m\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage.IsKrausDecomposition}\left(k\right)) \Leftrightarrow (\forall (x: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), (\sum_{a: \operatorname{Fin}\left(m\right)} (((k\left(a\right)) \cdot (x)) \cdot (\operatorname{Matrix.conjTranspose}\left(k\left(a\right)\right))) = \operatorname{D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.wernerHolevo}\left((1: \mathbb{R}), x\right)))))$$

*Formalization.* `D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage.IsKrausDecomposition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Milajiguli Rexiti; Samad Khabbazi Oskouei; Stefano Mancini (2024). *On the effectiveness of Bayesian discrete feedback for quantum information reclaiming*. DOI: [10.1007/s11128-024-04467-x](https://doi.org/10.1007/s11128-024-04467-x). URL: <https://arxiv.org/abs/2402.18941v1>.

*Commentary.*

A family k indexed by Fin m is a Kraus decomposition when its operator sum agrees, on every complex three-by-three matrix x, with the Werner–Holevo map at the real parameter 1. That map sends x to one half of tr(x)I minus one half of the transpose of x. The adjoint in the operator sum is the conjugate transpose. The equality is required on all matrices, rather than only on density matrices.

**Definition 1.2 (Two-step Markovian entanglement fidelity).**

$$\forall (m_{1}: \mathbb{N}), (\forall (m_{2}: \mathbb{N}), (\forall (k_{1}: (\operatorname{Fin}\left(m_{1}\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), (\forall (k_{2}: (\operatorname{Fin}\left(m_{2}\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage.markovFidelity}\left(k_{1}, k_{2}\right): \mathbb{R}) = (\frac{(1: \mathbb{R})}{(9: \mathbb{R})}) \cdot (\sum_{a: \operatorname{Fin}\left(m_{1}\right)} (\sum_{b: \operatorname{Fin}\left(m_{2}\right)} ((\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((\operatorname{CFC.abs}\left(\left(k_{2}\right)\left(b\right)\right)) \cdot (\operatorname{CFC.abs}\left(\left(k_{1}\right)\left(a\right)\right))\right)\right))^{(2: \mathbb{N})})))))))$$

*Formalization.* `D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage.markovFidelity` (`✓ std3`).

*Citation.* Milajiguli Rexiti; Samad Khabbazi Oskouei; Stefano Mancini (2024). *On the effectiveness of Bayesian discrete feedback for quantum information reclaiming*. DOI: [10.1007/s11128-024-04467-x](https://doi.org/10.1007/s11128-024-04467-x). URL: <https://arxiv.org/abs/2402.18941v1>.

*Commentary.*

Markovian feedback corrects each step separately. The resulting branch operator is the product of the absolute values of the second and first Kraus operators, in that order. The fidelity is one ninth of the sum of squared real traces of those products. Here CFC.abs T is the positive square root of TᴴT. This is the two-step Markovian formula in EffOfBayesianFB.tex, lines 245–249, with dimension d equal to 3. The displayed real part makes the real-valued expression explicit. The definition accepts arbitrary finite matrix families; the comparison below assumes they represent the channel.

**Definition 1.3 (Two-step Bayesian entanglement fidelity).**

$$\forall (m_{1}: \mathbb{N}), (\forall (m_{2}: \mathbb{N}), (\forall (k_{1}: (\operatorname{Fin}\left(m_{1}\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), (\forall (k_{2}: (\operatorname{Fin}\left(m_{2}\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage.bayesFidelity}\left(k_{1}, k_{2}\right): \mathbb{R}) = (\frac{(1: \mathbb{R})}{(9: \mathbb{R})}) \cdot (\sum_{a: \operatorname{Fin}\left(m_{1}\right)} (\sum_{b: \operatorname{Fin}\left(m_{2}\right)} ((\operatorname{D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm}\left((\left(k_{2}\right)\left(b\right)) \cdot (\operatorname{CFC.abs}\left(\left(k_{1}\right)\left(a\right)\right))\right))^{(2: \mathbb{N})})))))))$$

*Formalization.* `D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage.bayesFidelity` (`✓ std3`).

*Citation.* Milajiguli Rexiti; Samad Khabbazi Oskouei; Stefano Mancini (2024). *On the effectiveness of Bayesian discrete feedback for quantum information reclaiming*. DOI: [10.1007/s11128-024-04467-x](https://doi.org/10.1007/s11128-024-04467-x). URL: <https://arxiv.org/abs/2402.18941v1>.

*Commentary.*

Bayesian feedback corrects the accumulated branch after the first correction. For outcomes a and b the matrix is k₂ b times the absolute value of k₁ a. Its trace norm is the real trace of the positive square root of its adjoint times itself. The fidelity sums the squares of these trace norms and divides by 9. This is EffOfBayesianFB.tex, lines 250–253, specialized to dimension 3. As with the Markovian expression, the definition itself imposes no Kraus-decomposition hypothesis.

**Theorem 1.4 (A strict Bayesian advantage).**

$$(\forall (m_{1}: \mathbb{N}), (\forall (m_{2}: \mathbb{N}), (\forall (k_{1}: (\operatorname{Fin}\left(m_{1}\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), (\forall (k_{2}: (\operatorname{Fin}\left(m_{2}\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage.IsKrausDecomposition}\left(k_{1}\right)) \to ((\operatorname{D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage.IsKrausDecomposition}\left(k_{2}\right)) \to (\operatorname{D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage.markovFidelity}\left(k_{1}, k_{2}\right) \le \frac{(1: \mathbb{R})}{(2: \mathbb{R})}))))))) \land (\exists (l_{1}: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), (\exists (l_{2}: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage.IsKrausDecomposition}\left(l_{1}\right)) \land ((\operatorname{D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage.IsKrausDecomposition}\left(l_{2}\right)) \land (\frac{(1: \mathbb{R})}{(2: \mathbb{R})} < \operatorname{D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage.bayesFidelity}\left(l_{1}, l_{2}\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage.result` (`✓ std3`). ∎

*Resolves.* `Problems/rexiti-oskouei-mancini-2024-werner-holevo-bayesian-feedback` (proved) by `D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rexiti-oskouei-mancini-2024-werner-holevo-bayesian-feedback","declaration_gid":"D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Milajiguli Rexiti; Samad Khabbazi Oskouei; Stefano Mancini (2024). *On the effectiveness of Bayesian discrete feedback for quantum information reclaiming*. DOI: [10.1007/s11128-024-04467-x](https://doi.org/10.1007/s11128-024-04467-x). URL: <https://arxiv.org/abs/2402.18941v1>.

*Commentary.*

First consider arbitrary finite Kraus decompositions K₁ and K₂ of the channel. For a single decomposition K, apply its operator-sum identity to xxᴴ and evaluate the quadratic form on the conjugate of x. The channel side is zero, while the sum side is the sum over a of |xᵀ(K a)x|². Every summand is nonnegative, so every quadratic form vanishes. Coordinate vectors give zero diagonal entries, and sums of two distinct coordinate vectors give opposite off-diagonal entries. Thus every K a is antisymmetric.

Taking traces of the channel identity on matrix units gives the trace-preservation identity Σₐ(K a)ᴴ(K a) = I. Write A(z) for the matrix of the linear map y ↦ z × y. The antisymmetry gives K a = A(z a)/√2, with z a = √2((K a)₂₁,(K a)₀₂,(K a)₁₀). Substituting the cross-product matrices and comparing diagonal and off-diagonal entries yields Σₐ(z a)(z a)ᴴ = I. Hence both decompositions give such frames.

For V = zzᴴ and c = ‖z‖², direct multiplication gives A(z)ᴴA(z) = cI − V and V² = cV. If z is nonzero, put r = ‖z‖. The matrix rI − r⁻¹V equals r⁻¹(cI − V), is positive semidefinite, and squares to cI − V. Uniqueness of the positive square root therefore gives |A(z)/√2| = (rI − r⁻¹zzᴴ)/√2. The zero vector gives the zero matrix separately.

The rank-one trace identities are tr(zzᴴ) = ‖z‖² and tr(wwᴴzzᴴ) = (wᴴz)(zᴴw). Expanding the product of the two absolute values therefore gives, for nonzero w and z, tr(|A(w)/√2||A(z)/√2|) = (u + v/u)/2, where u = ‖w‖‖z‖ and v = |wᴴz|². Cauchy–Schwarz gives 0 ≤ v ≤ u², and consequently (u + v/u)² ≤ u² + 3v. Thus the squared real trace is at most (‖w‖²‖z‖² + 3|wᴴz|²)/4. The same bound holds when either vector is zero.

Taking traces of each frame identity gives Σₐ‖z a‖² = Σᵦ‖w b‖² = 3. Contracting the second frame against a rank-one matrix gives Σᵦ|(w b)ᴴ(z a)|² = ‖z a‖², so the double sum of squared overlaps is 3. The double sum of products of squared norms is 9. Summing the preceding pairwise bound and multiplying by 1/9 gives markovFidelity K₁ K₂ ≤ (9 + 3·3)/36 = 1/2.

For the existential assertion choose l₁ i = A(eᵢ)/√2 and l₂ j = A(wⱼ)/√2, where eᵢ are the three coordinate vectors and w₀ = (2,2,−1)/3, w₁ = (−1,2,2)/3, w₂ = (2,−1,2)/3. Expanding all matrix entries of the two operator sums shows that each equals the Werner–Holevo map. Both chosen families therefore satisfy IsKrausDecomposition.

The first family's absolute values are (I − eᵢeᵢᴴ)/√2. For each i,j set p = I − eᵢeᵢᴴ, b = A(wⱼ)p and s = |Re(wⱼ)ᵢ|. The matrix root = s p/(2(1+s)) + bᴴb/(2(1+s)) is positive semidefinite: p = pᴴp, bᴴb is positive semidefinite, and both coefficients are nonnegative. For the nine pairs, direct entrywise calculation gives root² = (b/2)ᴴ(b/2) and Re tr(root) = (1+s)/2. Since l₂ j |l₁ i| = b/2, uniqueness of the positive square root identifies root with the absolute value of that branch.

There are six entries with s = 2/3 and three with s = 1/3. Substitution in the Bayesian fidelity gives (6(5/6)² + 3(2/3)²)/9 = 11/18 > 1/2. The universal Markovian bound and these two three-operator decompositions give the two conjuncts of the assertion. This supplies a channel with a strict Bayesian advantage as requested in EffOfBayesianFB.tex, lines 910–911.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage.IsKrausDecomposition`
- Truth anchor: `D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage.bayesFidelity`
- Truth anchor: `D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage.markovFidelity`
- Truth anchor: `D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum](../Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.md)
- Dependency: [D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction](../Information/SeparableStateLocalUnitaryStabilizerObstruction.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding](../QuantumChannels/NoisyWernerHolevoLindbladEmbedding.md)
- Dependency: [D5/S3/Weil/BurnolGram/QuantitativeMultiOrbitWeilNegativeCertificate](../../Weil/BurnolGram/QuantitativeMultiOrbitWeilNegativeCertificate.md)
