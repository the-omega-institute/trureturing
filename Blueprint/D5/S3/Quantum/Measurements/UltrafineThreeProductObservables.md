# Pairwise and joint entanglement detection

## Abstract

Three Hermitian product observables have useless pairs and a useful triple on two qutrits.

**Definition 1.1 (Separable matrices).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (\sigma: \operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.IsSeparable}\left(\sigma\right)) \Leftrightarrow (\sigma \in \operatorname{convexHull}\left(\mathbb{R}, \{(\tau: \operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), \mathbb{C}\right)) \mid \exists (a: (\operatorname{Fin}\left(m\right)) \to (\mathbb{C})), (\exists (b: (\operatorname{Fin}\left(n\right)) \to (\mathbb{C})), ((\operatorname{dotProduct}\left(\operatorname{star}\left(a\right), a\right) = (1: \mathbb{C})) \land ((\operatorname{dotProduct}\left(\operatorname{star}\left(b\right), b\right) = (1: \mathbb{C})) \land (\tau = \operatorname{D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity}\left(\lambda (p: (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right))) \mapsto (a\left(\operatorname{Prod.fst}\left(p\right)\right) \cdot b\left(\operatorname{Prod.snd}\left(p\right)\right))\right)))))\}\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurements/UltrafineThreeProductObservables.IsSeparable` (`✓ std3`).

*Citation.* Gachechiladze, Mariami; Wyderka, Nikolai; Gühne, Otfried (2018). *The structure of ultrafine entanglement witnesses*. DOI: [10.1088/1751-8121/aad3dc](https://doi.org/10.1088/1751-8121/aad3dc). URL: <https://arxiv.org/abs/1805.06404v2>.

*Commentary.*

For natural dimensions m and n, a complex matrix on Fin m × Fin n is separable when it belongs to the real convex hull of projectors onto normalized product vectors. The source defines separable states as the convex hull of pure product states in uew-iop-revision.tex, lines 113–114. Convex hull here means finite convex combinations.

The projector is `D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity`: its entries are the vector coordinates times the conjugate coordinates. The two normalization equations use complex-valued dot products and the complex scalar one. The definition permits unequal dimensions, including zero dimensions.

**Definition 1.2 (Expectation values reproducible by separable states).**

$$\forall (d: \mathbb{N}), (\forall (\iota: \operatorname{Type}*), (\forall (obs: (\iota) \to (\operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right))), (\forall (s: \operatorname{Finset}\left(\iota\right)), ((\operatorname{D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.IsUseless}\left(obs, s\right)) \Leftrightarrow (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation.IsDensity}\left(\rho\right)) \to (\exists (\sigma: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation.IsDensity}\left(\sigma\right)) \land ((\operatorname{D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.IsSeparable}\left(\sigma\right)) \land (\forall (i: \iota), ((i \in s) \to (\operatorname{Matrix.trace}\left(\sigma \cdot obs\left(i\right)\right) = \operatorname{Matrix.trace}\left(\rho \cdot obs\left(i\right)\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/UltrafineThreeProductObservables.IsUseless` (`✓ std3`).

*Citation.* Gachechiladze, Mariami; Wyderka, Nikolai; Gühne, Otfried (2018). *The structure of ultrafine entanglement witnesses*. DOI: [10.1088/1751-8121/aad3dc](https://doi.org/10.1088/1751-8121/aad3dc). URL: <https://arxiv.org/abs/1805.06404v2>.

*Commentary.*

A finite selection s from an arbitrarily indexed family obs is useless when every density matrix has a separable density matrix with the same complex trace expectation for every selected observable. Both parties have dimension d. The same matrix σ must reproduce all the selected expectations simultaneously. The source describes uselessness in uew-iop-revision.tex, lines 504–507.

Density means positive semidefinite with trace equal to one, using `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.IsDensity`. This predicate places no Hermitian or product condition on obs; those conditions are supplied separately in the existence statement.

**Definition 1.3 (Three product observables with no useful pair).**

$$(\operatorname{D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.claim}) \Leftrightarrow (\exists (a: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), (\exists (b: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), ((\forall (i: \operatorname{Fin}\left(3\right)), ((\operatorname{Matrix.IsHermitian}\left(a\left(i\right)\right)) \land (\operatorname{Matrix.IsHermitian}\left(b\left(i\right)\right)))) \land ((\forall (i: \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(3\right)), ((i \ne j) \to (\operatorname{D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.IsUseless}\left(\lambda (k: \operatorname{Fin}\left(3\right)) \mapsto (\operatorname{Matrix.kronecker}\left(a\left(k\right), b\left(k\right)\right)), (\{i, j\}: \operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right))\right))))) \land (\neg (\operatorname{D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.IsUseless}\left(\lambda (k: \operatorname{Fin}\left(3\right)) \mapsto (\operatorname{Matrix.kronecker}\left(a\left(k\right), b\left(k\right)\right)), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right))\right)))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/UltrafineThreeProductObservables.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gachechiladze, Mariami; Wyderka, Nikolai; Gühne, Otfried (2018). *The structure of ultrafine entanglement witnesses*. DOI: [10.1088/1751-8121/aad3dc](https://doi.org/10.1088/1751-8121/aad3dc). URL: <https://arxiv.org/abs/1805.06404v2>.

*Commentary.*

There exist two families a and b of three Hermitian three-by-three complex matrices. Every pair of distinct indices gives a useless pair of their Kronecker products, whereas the whole triple is useful. The indices are the elements of Fin 3, namely zero, one and two. This answers the source's request to identify such a triple in uew-iop-revision.tex, lines 748–752, by fixing both local dimensions to three. Usefulness means that some density matrix has no separable density matrix matching all three expectations; it asserts neither a classification nor a noise bound.

**Theorem 1.4 (An explicit two-qutrit triple).**

$$\exists (a: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), (\exists (b: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right))), ((\forall (i: \operatorname{Fin}\left(3\right)), ((\operatorname{Matrix.IsHermitian}\left(a\left(i\right)\right)) \land (\operatorname{Matrix.IsHermitian}\left(b\left(i\right)\right)))) \land ((\forall (i: \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(3\right)), ((i \ne j) \to (\operatorname{D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.IsUseless}\left(\lambda (k: \operatorname{Fin}\left(3\right)) \mapsto (\operatorname{Matrix.kronecker}\left(a\left(k\right), b\left(k\right)\right)), (\{i, j\}: \operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right))\right))))) \land (\neg (\operatorname{D5.S3.Quantum.Measurements.UltrafineThreeProductObservables.IsUseless}\left(\lambda (k: \operatorname{Fin}\left(3\right)) \mapsto (\operatorname{Matrix.kronecker}\left(a\left(k\right), b\left(k\right)\right)), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/UltrafineThreeProductObservables.result` (`✓ std3`). ∎

*Resolves.* `Problems/gachechiladze-wyderka-guhne-2018-three-product-observables` (proved) by `D5/S3/Quantum/Measurements/UltrafineThreeProductObservables.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gachechiladze-wyderka-guhne-2018-three-product-observables","declaration_gid":"D5/S3/Quantum/Measurements/UltrafineThreeProductObservables.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gachechiladze, Mariami; Wyderka, Nikolai; Gühne, Otfried (2018). *The structure of ultrafine entanglement witnesses*. DOI: [10.1088/1751-8121/aad3dc](https://doi.org/10.1088/1751-8121/aad3dc). URL: <https://arxiv.org/abs/1805.06404v2>.

*Commentary.*

Set δ = 1/100. On the first party take A₀ = diag(1,1,δ), A₁ = X ⊕ [δ] and A₂ = Z ⊕ [δ], where X has rows (0,1), (1,0), and Z = diag(1,−1). On the second party take B₀ with rows (2,1,0), (1,2,1), (0,1,2), B₁ = diag(1,2,3), and B₂ = diag(1,4,9). All entries are complex scalars. Define Mᵢ = Aᵢ ⊗ Bᵢ and H = M₀ + M₁ + M₂. The six local matrices are real symmetric, hence Hermitian.

First consider a matrix of the form Σₖ |uₖ⟩⟨uₖ| ⊗ cₖ, where the uₖ are columns of a unitary matrix, each cₖ is positive semidefinite, and the total trace is one. Spectrally decompose each cₖ. Its nonnegative eigenvalues are weights for normalized product projectors, and the trace condition makes their total weight one. The Kronecker product of two rank-one projectors is the projector onto the product vector, so this matrix belongs to the defining convex hull.

Suppose a unitary matrix simultaneously diagonalizes the selected first-party factors. Let qₖ = |uₖ⟩⟨uₖ| and pₖ = qₖ ⊗ I. For a density matrix ρ, put cₖ = Vₖ*ρVₖ, where Vₖ sends b to uₖ ⊗ b, and set σ = Σₖ qₖ ⊗ cₖ. Each cₖ is positive semidefinite and σ = Σₖ pₖρpₖ. The pₖ are Hermitian orthogonal projections summing to I, so this unread projective measurement preserves trace and positivity. The block decomposition just proved makes σ separable. Each pₖ commutes with every selected product observable. Cyclicity of trace, pₖ² = pₖ and Σₖ pₖ = I therefore show that σ preserves all their expectations.

If the selected second-party factors are simultaneously diagonal instead, interchange the tensor coordinates, apply the same construction, and interchange them back. This real linear reindexing preserves products, trace and positivity; it also sends each normalized product projector to a normalized product projector and therefore preserves their convex hull.

For indices zero and one, use the unitary which is the Hadamard matrix on the first two coordinates and fixes the third: its nontrivial entries are ±1/√2. It simultaneously diagonalizes A₀ and A₁. For zero and two, A₀ and A₂ are already diagonal. For one and two, B₁ and B₂ are already diagonal. These three cases and symmetry of the two-element selection prove uselessness for every distinct pair. The source's commuting-factor observation is in uew-iop-revision.tex, lines 679–683; the matrices and the dephasing construction here specify the example explicitly.

Next H is Hermitian, so choose a normalized eigenvector g for its least real eigenvalue μ. The spectral lower bound gives H − (μ : ℂ)I positive semidefinite. Its diagonal entry at the tensor coordinate (1,2) is −7 − μ, hence μ ≤ −7 < 0. For the third first-party coordinate, the relevant second-party sum is B₀ + B₁ + B₂ = diag(3,6,13) + vv* + ww*, with v = (1,1,0) and w = (0,1,1). This sum is positive semidefinite.

Assume that a normalized product vector a ⊗ b were an eigenvector for this negative μ. The equation in its third first-party coordinate is a₂(B₀ + B₁ + B₂)b = 100(μ : ℂ)a₂b. If a₂ were nonzero, cancellation and the normalization of b would contradict the positive semidefinite quadratic form of B₀ + B₁ + B₂. Thus a₂ = 0, and normalization ensures a₀ ≠ 0 or a₁ ≠ 0.

Eliminate the common terms from the two remaining first-party equations. With c = a₁² − a₀², e = 2a₀a₁ and w = (1,2,3), the resulting equations are (c wᵢ + e wᵢ²)bᵢ = 0 for every second-party coordinate i. If bᵢ and bⱼ are nonzero at distinct coordinates, the determinant wᵢwⱼ² − wⱼwᵢ² is nonzero: for increasing indices its values are 2, 6 and 6. The two equations force c = e = 0, hence a₀ = a₁ = 0, a contradiction. Consequently b has exactly one nonzero coordinate k. If k is zero or two, the equations at coordinate one force a₀ = a₁ = 0; if k is one, use coordinate zero. These equations use the adjacent off-diagonal entries of B₀. This excludes every normalized product eigenvector at μ.

For a normalized product vector v, the positive semidefinite matrix Q = H − (μ : ℂ)I now satisfies Qv ≠ 0. The zero-quadratic-form criterion for positive semidefinite matrices gives Re(v*Qv) > 0. The rank-one expectation identity from `D5/S3/Quantum/PureState/PureStateHandshake.pure_state_handshake` then gives Re Tr(|v⟩⟨v|H) > μ. The real functional σ ↦ Re Tr(σH) is linear, and the strict half-space above μ is convex. It contains every normalized product projector, so it contains their convex hull: every separable σ has energy strictly above μ.

Finally ρ = |g⟩⟨g| is a density matrix and Tr(ρH) = (μ : ℂ). If a separable density matrix σ matched all three expectations of ρ, adding those three equalities would give Tr(σH) = (μ : ℂ), contradicting the strict separable energy bound. The displayed families therefore have useless pairs and a useful triple.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.IsDensity`
- Truth anchor: `D5/S3/Quantum/Measurements/UltrafineThreeProductObservables.IsSeparable`
- Truth anchor: `D5/S3/Quantum/Measurements/UltrafineThreeProductObservables.IsUseless`
- Truth anchor: `D5/S3/Quantum/Measurements/UltrafineThreeProductObservables.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/UltrafineThreeProductObservables.result`
- Truth anchor: `D5/S3/Quantum/PureState/PureStateHandshake.pure_state_handshake`
- Truth anchor: `D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity`
- Dependency: [D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation](../Entanglement/StructuredNegativityCoincidenceRefutation.md)
- Dependency: [D5/S3/Quantum/Measurement/ErrorDisturbanceEndpointRefutation](../Measurement/ErrorDisturbanceEndpointRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation](../QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.md)
