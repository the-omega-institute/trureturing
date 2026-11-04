# Lindblad embeddability of the noisy Werner-Holevo channel

## Abstract

On the interval from zero to two thirds, the noisy qutrit Werner-Holevo channel is a GKSL exponential exactly at zero noise.

**Definition 1.1 (The noisy qutrit Werner-Holevo map).**

$$\forall (x: \mathbb{R}), ((\operatorname{D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.wernerHolevo}\left(x\right): \operatorname{Module.End}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right)) = (((((1: \mathbb{C})) - ((\operatorname{Complex.ofReal}\left(x\right): \mathbb{C}))) \cdot ((\operatorname{LinearMap.id}: \operatorname{Module.End}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right)))) - ((\frac{(\operatorname{Complex.ofReal}\left(x\right): \mathbb{C})}{(2: \mathbb{C})}) \cdot (\operatorname{LinearEquiv.toLinearMap}\left(\operatorname{Matrix.transposeLinearEquiv}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}, \mathbb{C}\right)\right)))) + ((\frac{(\operatorname{Complex.ofReal}\left(x\right): \mathbb{C})}{(2: \mathbb{C})}) \cdot (\operatorname{LinearMap.smulRight}\left(\operatorname{Matrix.traceLinearMap}\left(\operatorname{Fin}\left(3\right), \mathbb{C}, \mathbb{C}\right), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.wernerHolevo` (`✓ std3`).

*Citation.* Shayan Roofeh; Vahid Karimipour (2024). *Noisy Werner-Holevo channel and its properties*. DOI: [10.1103/PhysRevA.109.052620](https://doi.org/10.1103/PhysRevA.109.052620). URL: <https://arxiv.org/abs/2310.15353v7>.

*Commentary.*

Equation (lambdax), TeX line 153, combines the identity channel with the qutrit Werner-Holevo channel. The formula acts on all complex three by three matrices, using the ordinary transpose and matrix trace. The real parameter x is included in the complex scalars by Complex.ofReal. The source takes x between zero and one; the displayed linear map is defined for every real x.

**Definition 1.2 (Finite GKSL generators).**

$$\forall (G: \operatorname{Module.End}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right)), (((\operatorname{D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.IsGKSLGenerator}\left(G\right): \operatorname{Prop})) \Leftrightarrow (\exists (m: \mathbb{N}), (\exists (H: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), (\exists (V: (\operatorname{Fin}\left(m\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), ((\operatorname{Matrix.IsHermitian}\left(H\right)) \land (\forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), (G\left(X\right) = ((-\operatorname{Complex.I}) \cdot (((H) \cdot (X)) - ((X) \cdot (H)))) + (\sum (k: \operatorname{Fin}\left(m\right)), ((((V\left(k\right)) \cdot (X)) \cdot (\operatorname{Matrix.conjTranspose}\left(V\left(k\right)\right))) - ((\frac{(1: \mathbb{C})}{(2: \mathbb{C})}) \cdot ((((\operatorname{Matrix.conjTranspose}\left(V\left(k\right)\right)) \cdot (V\left(k\right))) \cdot (X)) + ((X) \cdot (((\operatorname{Matrix.conjTranspose}\left(V\left(k\right)\right)) \cdot (V\left(k\right))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.IsGKSLGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shayan Roofeh; Vahid Karimipour (2024). *Noisy Werner-Holevo channel and its properties*. DOI: [10.1103/PhysRevA.109.052620](https://doi.org/10.1103/PhysRevA.109.052620). URL: <https://arxiv.org/abs/2310.15353v7>.

*Commentary.*

A complex-linear generator has a Hermitian Hamiltonian H and a finite family V of jump matrices. Its Hamiltonian part is minus the imaginary unit times the commutator with H. Each jump contributes conjugation by V followed by subtraction of half the anticommutator with its adjoint product. The natural number m may be zero. This specifies the meaning of Lindbladian dynamics in the question at TeX line 249.

**Definition 1.3 (The exponential of a generator).**

$$\forall (G: \operatorname{Module.End}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right)), ((\operatorname{D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.generatorExp}\left(G\right): \operatorname{Module.End}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right)) = (\operatorname{AlgEquiv.symm}\left(\operatorname{LinearMap.toMatrixAlgEquiv}\left(\operatorname{Matrix.stdBasis}\left(\mathbb{C}, \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right)\right)\right))\left(\operatorname{NormedSpace.exp}\left((\operatorname{LinearMap.toMatrixAlgEquiv}\left(\operatorname{Matrix.stdBasis}\left(\mathbb{C}, \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right)\right)\right))\left(G\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.generatorExp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shayan Roofeh; Vahid Karimipour (2024). *Noisy Werner-Holevo channel and its properties*. DOI: [10.1103/PhysRevA.109.052620](https://doi.org/10.1103/PhysRevA.109.052620). URL: <https://arxiv.org/abs/2310.15353v7>.

*Commentary.*

The matrix-unit basis identifies a complex-linear endomorphism of the matrix space with a nine by nine complex matrix. Take the ordinary matrix exponential and transport it back through the inverse algebra equivalence. The exponential is evaluated at time one.

**Definition 1.4 (Embeddability on the remaining interval).**

$$((\operatorname{D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.claim}: \operatorname{Prop})) \Leftrightarrow (\forall (x: \mathbb{R}), ((x \in \operatorname{Set.Icc}\left((0: \mathbb{R}), \frac{(2: \mathbb{R})}{(3: \mathbb{R})}\right)) \to ((\exists (G: \operatorname{Module.End}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right)), ((\operatorname{D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.IsGKSLGenerator}\left(G\right)) \land (\operatorname{D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.generatorExp}\left(G\right) = \operatorname{D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.wernerHolevo}\left(x\right)))) \Leftrightarrow (x = (0: \mathbb{R})))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shayan Roofeh; Vahid Karimipour (2024). *Noisy Werner-Holevo channel and its properties*. DOI: [10.1103/PhysRevA.109.052620](https://doi.org/10.1103/PhysRevA.109.052620). URL: <https://arxiv.org/abs/2310.15353v7>.

*Commentary.*

The question at TeX line 249 concerns parameters between zero and two thirds, including both endpoints. For every such real x, existence of a finite GKSL generator whose exponential equals the noisy channel is equivalent to x being zero. Equality here is equality of linear maps on the entire complex matrix space.

**Theorem 1.5 (Exactly zero noise is Lindblad embeddable).**

$$\forall (x: \mathbb{R}), ((x \in \operatorname{Set.Icc}\left((0: \mathbb{R}), \frac{(2: \mathbb{R})}{(3: \mathbb{R})}\right)) \to ((\exists (G: \operatorname{Module.End}\left(\mathbb{C}, \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)\right)), ((\operatorname{D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.IsGKSLGenerator}\left(G\right)) \land (\operatorname{D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.generatorExp}\left(G\right) = \operatorname{D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding.wernerHolevo}\left(x\right)))) \Leftrightarrow (x = (0: \mathbb{R}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.result` (`✓ std3`). ∎

*Resolves.* `Problems/roofeh-karimipour-2024-werner-holevo-lindblad-embedding` (proved) by `D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"roofeh-karimipour-2024-werner-holevo-lindblad-embedding","declaration_gid":"D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shayan Roofeh; Vahid Karimipour (2024). *Noisy Werner-Holevo channel and its properties*. DOI: [10.1103/PhysRevA.109.052620](https://doi.org/10.1103/PhysRevA.109.052620). URL: <https://arxiv.org/abs/2310.15353v7>.

*Commentary.*

The zero endomorphism is a GKSL generator: take m equal to zero, the zero Hamiltonian, and the empty jump family. Its exponential and the channel at x equal to zero are both the identity map.

Every generator exponential is invertible, since its matrix exponential is a unit and the algebra equivalence preserves units. An eigenvector of G with eigenvalue μ is therefore an eigenvector of its exponential with eigenvalue exp(μ); this follows by passing to coordinates in the matrix-unit basis and back.

For an idempotent linear map P commuting with G, restrict G to the range W of P. The restriction is obtained by composing the inclusion of W, G, and the range restriction of P. If the exponential of G times P equals b times P for a positive real b, each eigenvalue μ of this restriction satisfies exp(μ) = b. Taking the complex norm gives exp(Re μ) = b, hence Re μ = log b. The characteristic polynomial splits over the complex numbers, so summing its roots gives real trace equal to the complex dimension of W times log b. Cyclicity of the linear-map trace identifies this trace with the real trace of G composed with P; the trace of an idempotent is the dimension of its range.

At x equal to two thirds the nonzero diagonal matrix with diagonal entries 1, minus 1, and 0 is sent to zero. Thus the endpoint channel cannot equal any generator exponential, which is injective.

Let P send X to (X + Xᵀ)/2 minus trace(X) times the identity divided by 3, and let Q send X to (X − Xᵀ)/2. Write s(G) and a(G) for the real endomorphism traces of G composed with P and Q, respectively. For the Hamiltonian commutator, s minus five times a is zero. For a single jump matrix V, the same difference is twice the sum of the squared complex norms of V₀₀ − V₁₁, V₀₀ − V₂₂, and V₁₁ − V₂₂, plus three times the sum of the squared complex norms of V₀₁ + V₁₀, V₀₂ + V₂₀, and V₁₂ + V₂₁. These identities follow by expanding the trace in the matrix-unit basis and the matrix entries of the two projections. Linearity of trace and nonnegativity of every squared norm imply s(G) − 5a(G) is nonnegative for every GKSL generator.

The generator commutes with its exponential. Every GKSL generator has trace(G(X)) equal to zero: cyclicity of the matrix trace cancels both the commutator and each jump term. The noisy channel fixes the identity. If x is nonzero and its channel equals the exponential of G, commutation makes G applied to the identity a fixed matrix of that channel. Its trace is zero, and the equations for its transposed entries force every entry to vanish. Applying commutation to an arbitrary matrix then shows that G commutes with transposition. Together with trace zero and G applied to the identity equal to zero, this proves that G commutes with both P and Q.

Direct matrix-entry calculations show that P and Q are idempotent with traces 5 and 3. The noisy channel acts on their ranges by b = 1 − 3x/2 and c = 1 − x/2, respectively, as in the source's spectral formulas at TeX lines 236–247. For x strictly between zero and two thirds both scalars are positive. The preceding restriction argument gives s(G) = 5 log b and a(G) = 3 log c.

Strict Bernoulli inequality with increment minus x/2 and exponent 3 gives b strictly less than c cubed. Monotonicity of the logarithm and the logarithm of a power yield 5 log b strictly less than 15 log c. This contradicts s(G) − 5a(G) being nonnegative. For an x in the closed interval, any nonzero x is positive and lies either in this interior or at the excluded endpoint. Both alternatives are impossible, and the zero generator supplies the converse.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.IsGKSLGenerator`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.generatorExp`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding.wernerHolevo`
- Dependency: [D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation](../Dynamics/DissipatorSpectralDiskRefutation.md)
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](../Dynamics/EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace](TwoPositiveTransitionTrace.md)
