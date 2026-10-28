# Partial entanglement annihilation fails under aligned tensor products

## Abstract

Two non-local channels with Schmidt-number-two outputs can have an aligned tensor product with a Schmidt-rank-four output.

**Definition 1.1 (Excluding products of individual channels).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(e: \operatorname{MatrixMap}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.SchmidtNumber.PartiallyEntanglementAnnihilatingTensorRefutation.NonLocal}\left(e\right)\right) \Leftrightarrow \left(\neg \left(\exists \left(e_{1}: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\exists \left(e_{2}: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.IsCPTP}\left(e_{1}\right)\right) \land \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.IsCPTP}\left(e_{2}\right)\right) \land \left(e = \operatorname{MatrixMap.kron}\left(e_{1}, e_{2}\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.NonLocal` (`✓ std3`).

*Citation.* Bivas Mallick; Nirman Ganguly; A. S. Majumdar (2026). *On the characterization of partially entanglement breaking and annihilating channels*. DOI: [10.1063/5.0274921](https://doi.org/10.1063/5.0274921). URL: <https://arxiv.org/abs/2411.19315v2>.

*Commentary.*

A linear map on the bipartite d by d system is non-local when it cannot be expressed as the tensor product of two completely positive, trace-preserving maps on the individual d-dimensional systems. This is the distinction in Section IV, main.tex line 630. The predicate only excludes such a factorization; complete positivity and trace preservation of the bipartite map are separate conditions.

**Definition 1.2 (Non-local partial entanglement annihilation).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(r: \mathbb{N}\right), \left(\forall \left(e: \operatorname{MatrixMap}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.SchmidtNumber.PartiallyEntanglementAnnihilatingTensorRefutation.IsPEA}\left(d, r, e\right)\right) \Leftrightarrow \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.IsCPTP}\left(e\right)\right) \land \left(\left(\operatorname{D5.S3.Quantum.Entanglement.SchmidtNumber.PartiallyEntanglementAnnihilatingTensorRefutation.NonLocal}\left(e\right)\right) \land \left(\left(r < d\right) \land \left(\forall \left(\rho: \operatorname{D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.BipartiteOp}\left(d\right)\right), \left(\left(\operatorname{Matrix.PosSemidef}\left(\rho\right)\right) \to \left(\left(\operatorname{Matrix.trace}\left(\rho\right) = \left(1: \mathbb{C}\right)\right) \to \left(\operatorname{D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.SchmidtNumberLE}\left(\operatorname{DFunLike.coe}\left(e, \rho\right), r\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.IsPEA` (`✓ std3`).

*Citation.* Bivas Mallick; Nirman Ganguly; A. S. Majumdar (2026). *On the characterization of partially entanglement breaking and annihilating channels*. DOI: [10.1063/5.0274921](https://doi.org/10.1063/5.0274921). URL: <https://arxiv.org/abs/2411.19315v2>.

*Commentary.*

A non-local r-partially entanglement annihilating channel is completely positive and trace preserving, is non-local, has r strictly below d, and sends every positive semidefinite trace-one input to an operator of Schmidt number at most r. This is Section IV, main.tex line 632. SchmidtNumberLE expresses the existence of a finite convex decomposition into normalized pure states whose coefficient matrices all have rank at most r, corresponding to the Schmidt-number definition in Section II, lines 261–265.

**Definition 1.3 (The tensor product across the aligned split).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(e: \operatorname{MatrixMap}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right), \left(\forall \left(f: \operatorname{MatrixMap}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Quantum.Entanglement.SchmidtNumber.PartiallyEntanglementAnnihilatingTensorRefutation.alignedTensor}\left(e, f\right) = \left(\operatorname{let} a := \operatorname{Equiv.trans}\left(\operatorname{Equiv.prodProdProdComm}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \operatorname{Equiv.prodCongr}\left(\operatorname{finProdFinEquiv}, \operatorname{finProdFinEquiv}\right)\right); \left(\operatorname{let} t := \operatorname{Matrix.reindexLinearEquiv}\left(\mathbb{C}, \mathbb{C}, a, a\right); \operatorname{LinearMap.comp}\left(\operatorname{LinearEquiv.toLinearMap}\left(t\right), \operatorname{LinearMap.comp}\left(\operatorname{MatrixMap.kron}\left(e, f\right), \operatorname{LinearEquiv.toLinearMap}\left(\operatorname{LinearEquiv.symm}\left(t\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.alignedTensor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bivas Mallick; Nirman Ganguly; A. S. Majumdar (2026). *On the characterization of partially entanglement breaking and annihilating channels*. DOI: [10.1063/5.0274921](https://doi.org/10.1063/5.0274921). URL: <https://arxiv.org/abs/2411.19315v2>.

*Commentary.*

The equivalence a first exchanges the middle two factors of the fourfold product and then identifies each pair of Fin d indices with Fin (d * d). The linear equivalence t reindexes both matrix indices by a. Conjugating the tensor product of e and f by t makes the two first subsystems one party and the two second subsystems the other party. Thus both parties have dimension d * d.

**Definition 1.4 (Closure at the same Schmidt-number threshold).**

$$\left(\operatorname{D5.S3.Quantum.Entanglement.SchmidtNumber.PartiallyEntanglementAnnihilatingTensorRefutation.claim}\right) \Leftrightarrow \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(r: \mathbb{N}\right), \left(\forall \left(e: \operatorname{MatrixMap}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right), \left(\forall \left(f: \operatorname{MatrixMap}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Entanglement.SchmidtNumber.PartiallyEntanglementAnnihilatingTensorRefutation.IsPEA}\left(d, r, e\right)\right) \to \left(\left(\operatorname{D5.S3.Quantum.Entanglement.SchmidtNumber.PartiallyEntanglementAnnihilatingTensorRefutation.IsPEA}\left(d, r, f\right)\right) \to \left(\operatorname{D5.S3.Quantum.Entanglement.SchmidtNumber.PartiallyEntanglementAnnihilatingTensorRefutation.IsPEA}\left(\left(d\right) \cdot \left(d\right), r, \operatorname{D5.S3.Quantum.Entanglement.SchmidtNumber.PartiallyEntanglementAnnihilatingTensorRefutation.alignedTensor}\left(e, f\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bivas Mallick; Nirman Ganguly; A. S. Majumdar (2026). *On the characterization of partially entanglement breaking and annihilating channels*. DOI: [10.1063/5.0274921](https://doi.org/10.1063/5.0274921). URL: <https://arxiv.org/abs/2411.19315v2>.

*Commentary.*

For all natural dimensions d and thresholds r, the assertion says that any two non-local r-partially entanglement annihilating channels remain in that class after taking their aligned tensor product. The threshold stays r while the local dimension becomes d * d. This is a precise closure assertion for the tensor-product question in the Conclusion, main.tex line 1167; the source asks the question without asserting this closure.

**Theorem 1.5 (Two qutrit channels disprove closure).**

$$\neg \left(\operatorname{D5.S3.Quantum.Entanglement.SchmidtNumber.PartiallyEntanglementAnnihilatingTensorRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mallick-ganguly-majumdar-2026-pea-tensor-nonclosure` (refuted) by `D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mallick-ganguly-majumdar-2026-pea-tensor-nonclosure","declaration_gid":"D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Bivas Mallick; Nirman Ganguly; A. S. Majumdar (2026). *On the characterization of partially entanglement breaking and annihilating channels*. DOI: [10.1063/5.0274921](https://doi.org/10.1063/5.0274921). URL: <https://arxiv.org/abs/2411.19315v2>.

*Commentary.*

Take d = 3 and r = 2. Let φ be the normalized vector (|00⟩ + |11⟩)/√2 and let R send X to Tr(X)|φ⟩⟨φ|. The coefficient matrix of φ is diagonal with entries 1/√2, 1/√2 and 0. Its two nonzero diagonal entries give rank two.

For each coordinate vector |j⟩ of the nine-dimensional input, use the Kraus operator |φ⟩⟨j|. Summing their actions gives exactly R, so R is completely positive. Its output trace equals the input trace because |φ⟩⟨φ| has trace one; hence R is trace preserving.

Suppose R were a tensor product of two individual channels. Evaluating it on |00⟩⟨00| would express |φ⟩⟨φ| as A ⊗ B, where A and B are the individual outputs on |0⟩⟨0|. The diagonal entries at (0,0) and (1,1) are both (1/√2)², which is nonzero, whereas the entry at (0,1) is zero. Thus A₀₀B₁₁ = 0. If A₀₀ = 0 then A₀₀B₀₀ is zero, and if B₁₁ = 0 then A₁₁B₁₁ is zero. Either case contradicts one of the two nonzero diagonal entries, so R is non-local.

On every trace-one input, R outputs |φ⟩⟨φ|. The one-term convex decomposition with weight one therefore gives Schmidt number at most two. Together with complete positivity, trace preservation, non-locality and 2 < 3, this makes R a non-local 2-partially entanglement annihilating channel.

Let ψ be φ ⊗ φ regrouped across the aligned split. In the Fin 9 coordinates its coefficient matrix is diagonal, with entry 1/2 at indices 0, 1, 3 and 4 and zero elsewhere. Its rank is therefore four.

For any normalized bipartite vector u, a convex decomposition of |u⟩⟨u| with coefficient ranks at most r forces the coefficient rank of u to be at most r. Indeed, nonnegative weights summing to one are individually at most one and include a positive weight. The pure-state decomposition property then identifies that component with z times u for a complex scalar z of norm one. Its coefficient matrix is z times the coefficient matrix of u; since z is nonzero, the ranks agree, giving the required rank bound.

Expanding the tensor product of the two trace-and-prepare maps on matrix units shows that it sends X to Tr(X) times (|φ⟩⟨φ| ⊗ |φ⟩⟨φ|). Reindexing preserves trace. On the aligned input |ψ⟩⟨ψ| this trace is one, and the reindexed output is |ψ⟩⟨ψ| itself, as follows by multiplying the vector coordinates.

If the aligned tensor product were non-local 2-partially entanglement annihilating, its Schmidt-number bound on the positive semidefinite trace-one input |ψ⟩⟨ψ| would give Schmidt number at most two for that same pure output. The pure-state rank bound would then imply 4 ≤ 2, a contradiction. Applying the closure assertion to d = 3, r = 2 and e = f = R would give precisely this impossible conclusion.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.IsPEA`
- Truth anchor: `D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.NonLocal`
- Truth anchor: `D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.alignedTensor`
- Truth anchor: `D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation](../GraphDensity/UniqueBasisFormationRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation](../../QuantumChannels/ChannelAssemblageLOSRRefutation.md)
