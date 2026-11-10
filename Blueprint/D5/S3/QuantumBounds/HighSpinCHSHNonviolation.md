# Nonviolation of CHSH for all high-spin components

## Abstract

Linear spin components obey the CHSH bound for every spin at least one.

**Definition 1.1 (Unit measurement directions).**

$$\forall (u: (\operatorname{Fin}\left(3\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.QuantumBounds.HighSpinCHSHNonviolation.unit}\left(u\right)) \Leftrightarrow ((((u\left(0\right))^{2}) + ((u\left(1\right))^{2})) + ((u\left(2\right))^{2}) = (1: \mathbb{R})))$$

*Formalization.* `D5/S3/QuantumBounds/HighSpinCHSHNonviolation.unit` (`✓ std3`).

*Citation.* Louis Hanotel and Elena R. Loubenets (2025). *Nonviolation of the CHSH inequality under local spin-1 measurements on two spin qutrits*. DOI: [10.1088/1402-4896/adcc66](https://doi.org/10.1088/1402-4896/adcc66). URL: <https://arxiv.org/abs/2503.05172v2>.

*Commentary.*

A direction is unit when the sum of the squares of its three real components is one. This is the unit-vector condition used for spin projections in the companion high-spin construction (arXiv:2412.03470v2, TeX lines 210–237).

**Definition 1.2 (The linear-spin CHSH operator).**

$$\forall (n: \mathbb{N}), (\forall (a c b d: (\operatorname{Fin}\left(3\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.QuantumBounds.HighSpinCHSHNonviolation.chshOperator}\left(n, a, c, b, d\right): \operatorname{Matrix}\left((\operatorname{Fin}\left((n) + (1)\right) \times \operatorname{Fin}\left((n) + (1)\right)), (\operatorname{Fin}\left((n) + (1)\right) \times \operatorname{Fin}\left((n) + (1)\right)), \mathbb{C}\right)) = (((\operatorname{Matrix.kroneckerMap}\left(\lambda (x1: \mathbb{C}) \mapsto (\lambda (x2: \mathbb{C}) \mapsto ((x1) \cdot (x2))), \operatorname{D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.spinComponent}\left(n, a\right), \operatorname{D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.spinComponent}\left(n, b\right)\right)) + (\operatorname{Matrix.kroneckerMap}\left(\lambda (x1: \mathbb{C}) \mapsto (\lambda (x2: \mathbb{C}) \mapsto ((x1) \cdot (x2))), \operatorname{D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.spinComponent}\left(n, a\right), \operatorname{D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.spinComponent}\left(n, d\right)\right))) + (\operatorname{Matrix.kroneckerMap}\left(\lambda (x1: \mathbb{C}) \mapsto (\lambda (x2: \mathbb{C}) \mapsto ((x1) \cdot (x2))), \operatorname{D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.spinComponent}\left(n, c\right), \operatorname{D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.spinComponent}\left(n, b\right)\right))) - (\operatorname{Matrix.kroneckerMap}\left(\lambda (x1: \mathbb{C}) \mapsto (\lambda (x2: \mathbb{C}) \mapsto ((x1) \cdot (x2))), \operatorname{D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.spinComponent}\left(n, c\right), \operatorname{D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.spinComponent}\left(n, d\right)\right))))$$

*Formalization.* `D5/S3/QuantumBounds/HighSpinCHSHNonviolation.chshOperator` (`✓ std3`).

*Citation.* Louis Hanotel and Elena R. Loubenets (2025). *Nonviolation of the CHSH inequality under local spin-1 measurements on two spin qutrits*. DOI: [10.1088/1402-4896/adcc66](https://doi.org/10.1088/1402-4896/adcc66). URL: <https://arxiv.org/abs/2503.05172v2>.

*Commentary.*

For four real measurement directions, this is the alternating sum of the four Kronecker products of their linear spin components. It is the operator in the source's CHSH expression (Final_Revision_Hanotel_Loubenets.tex, lines 108–115), with the spin observables described in the companion paper (TeX lines 253–261).

**Definition 1.3 (The high-spin nonviolation assertion).**

$$(\operatorname{D5.S3.QuantumBounds.HighSpinCHSHNonviolation.claim}\left(\right)) \Leftrightarrow (\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \Rightarrow (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left((n) + (1)\right) \times \operatorname{Fin}\left((n) + (1)\right)), (\operatorname{Fin}\left((n) + (1)\right) \times \operatorname{Fin}\left((n) + (1)\right)), \mathbb{C}\right)), ((\operatorname{Matrix.PosSemidef}\left(\rho\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(\rho\right) = (1: \mathbb{C})) \Rightarrow (\forall (a c b d: (\operatorname{Fin}\left(3\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.QuantumBounds.HighSpinCHSHNonviolation.unit}\left(a\right)) \Rightarrow ((\operatorname{D5.S3.QuantumBounds.HighSpinCHSHNonviolation.unit}\left(c\right)) \Rightarrow ((\operatorname{D5.S3.QuantumBounds.HighSpinCHSHNonviolation.unit}\left(b\right)) \Rightarrow ((\operatorname{D5.S3.QuantumBounds.HighSpinCHSHNonviolation.unit}\left(d\right)) \Rightarrow (\left\lVert \operatorname{Matrix.trace}\left((\rho) \cdot (\operatorname{D5.S3.QuantumBounds.HighSpinCHSHNonviolation.chshOperator}\left(n, a, c, b, d\right))\right) \right\rVert \le \frac{(\operatorname{Nat.cast}\left(n\right): \mathbb{R})^{2}}{(2: \mathbb{R})})))))))))))$$

*Formalization.* `D5/S3/QuantumBounds/HighSpinCHSHNonviolation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Louis Hanotel and Elena R. Loubenets (2025). *Nonviolation of the CHSH inequality under local spin-1 measurements on two spin qutrits*. DOI: [10.1088/1402-4896/adcc66](https://doi.org/10.1088/1402-4896/adcc66). URL: <https://arxiv.org/abs/2503.05172v2>.

*Commentary.*

For every natural n at least two, every positive semidefinite complex density matrix on the tensor product of two (n+1)-dimensional spaces, and every four unit real directions, the trace expectation of the linear-spin CHSH operator has norm at most the real cast of n squared divided by two. With n = 2s, this is the bound 2s² for spin s ≥ 1, addressing the open high-spin question stated in the source (Final_Revision_Hanotel_Loubenets.tex, line 201).

**Theorem 1.4 (Every high-spin linear-spin CHSH expectation obeys the bound).**

$$\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \Rightarrow (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left((n) + (1)\right) \times \operatorname{Fin}\left((n) + (1)\right)), (\operatorname{Fin}\left((n) + (1)\right) \times \operatorname{Fin}\left((n) + (1)\right)), \mathbb{C}\right)), ((\operatorname{Matrix.PosSemidef}\left(\rho\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(\rho\right) = (1: \mathbb{C})) \Rightarrow (\forall (a c b d: (\operatorname{Fin}\left(3\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.QuantumBounds.HighSpinCHSHNonviolation.unit}\left(a\right)) \Rightarrow ((\operatorname{D5.S3.QuantumBounds.HighSpinCHSHNonviolation.unit}\left(c\right)) \Rightarrow ((\operatorname{D5.S3.QuantumBounds.HighSpinCHSHNonviolation.unit}\left(b\right)) \Rightarrow ((\operatorname{D5.S3.QuantumBounds.HighSpinCHSHNonviolation.unit}\left(d\right)) \Rightarrow (\left\lVert \operatorname{Matrix.trace}\left((\rho) \cdot (\operatorname{D5.S3.QuantumBounds.HighSpinCHSHNonviolation.chshOperator}\left(n, a, c, b, d\right))\right) \right\rVert \le \frac{(\operatorname{Nat.cast}\left(n\right): \mathbb{R})^{2}}{(2: \mathbb{R})}))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/HighSpinCHSHNonviolation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanotel-loubenets-2025-high-spin-chsh-nonviolation` (proved) by `D5/S3/QuantumBounds/HighSpinCHSHNonviolation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanotel-loubenets-2025-high-spin-chsh-nonviolation","declaration_gid":"D5/S3/QuantumBounds/HighSpinCHSHNonviolation.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Louis Hanotel and Elena R. Loubenets (2025). *Nonviolation of the CHSH inequality under local spin-1 measurements on two spin qutrits*. DOI: [10.1088/1402-4896/adcc66](https://doi.org/10.1088/1402-4896/adcc66). URL: <https://arxiv.org/abs/2503.05172v2>.

*Commentary.*

Fix n, a positive semidefinite trace-one matrix ρ, and four unit directions. For each n-qubit slot, form the slot Pauli matrix associated with a direction. The Dicke map sends the (n+1)-dimensional spin basis into the symmetric n-qubit subspace; counting subsets of each cardinality proves that its adjoint times it is the identity.

The slot matrices are Hermitian involutions. Their diagonal and flip entries decompose into raising, lowering, and z parts. Counting subsets not containing the selected slot and using the binomial coefficient identities gives the compression formula: each slot matrix compresses to (2/n) times the corresponding linear spin component. Tensoring two Dicke maps therefore compresses the lifted four-slot CHSH operator to the stated spin CHSH operator, with the scalar factor (n/2)².

Use distinct slots for the two local settings. Operators on different slots commute, so the lifted CHSH operator is Hermitian and the commuting-pair CHSH identity gives its square as four times the identity. Conjugating ρ by the isometric dilation preserves positive semidefiniteness and trace one.

The Hermitian square gives an operator norm at most two, and the density-matrix expectation estimate bounds the norm of its trace expectation by that operator norm. Cyclicity of trace moves the dilation through the original expectation; multiplying by the norm of (n/2)² yields (n/2)²·2 = n²/2. This proves the claim for every n ≥ 2.

## References

- Truth anchor: `D5/S3/QuantumBounds/HighSpinCHSHNonviolation.chshOperator`
- Truth anchor: `D5/S3/QuantumBounds/HighSpinCHSHNonviolation.claim`
- Truth anchor: `D5/S3/QuantumBounds/HighSpinCHSHNonviolation.result`
- Truth anchor: `D5/S3/QuantumBounds/HighSpinCHSHNonviolation.unit`
- Dependency: [D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment](../Quantum/Contextuality/TemporalHardySpinAttainment.md)
- Dependency: [D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint](../Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint.md)
- Dependency: [D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound](../Quantum/Information/GeometricDiscordMutualCorrelationBound.md)
- Dependency: [D5/S3/QuantumBounds/LandauCommutingCollapse](LandauCommutingCollapse.md)
