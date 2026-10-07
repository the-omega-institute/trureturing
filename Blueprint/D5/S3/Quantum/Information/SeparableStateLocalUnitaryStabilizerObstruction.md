# Separable states outside every local-unitary stabilizer frame

## Abstract

A rank-two mixture of two nonorthogonal product states remains outside the full convex stabilizer hull under every local unitary.

**Definition 1.1 (Normalized pure vectors).**

$$\forall n \in \operatorname{Type},\; [\operatorname{Fintype}\left(n\right)] \forall x \in n \to \mathbb{C},\; (\operatorname{unitVector}\left(x\right)) \Leftrightarrow (\operatorname{dotProduct}\left(\operatorname{star}\left(x\right), x\right) = 1)$$

*Formalization.* `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.unitVector` (`✓ std3`).

*Citation.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

A pure vector has squared norm one. star is componentwise complex conjugation and dotProduct sums over the finite index type n. The Fintype argument is an instance, rather than a named mathematical variable.

**Definition 1.2 (Signed Hermitian two-qubit Paulis).**

$$\forall P \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{IsHermitianPauli}\left(P\right)) \Leftrightarrow (\exists a \in \operatorname{Pauli},\; \exists b \in \operatorname{Pauli},\; (P = \operatorname{Matrix.kronecker}\left(\operatorname{pauliMatrix}\left(a\right), \operatorname{pauliMatrix}\left(b\right)\right)) \lor (P = -(\operatorname{Matrix.kronecker}\left(\operatorname{pauliMatrix}\left(a\right), \operatorname{pauliMatrix}\left(b\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.IsHermitianPauli` (`✓ std3`).

*Citation.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

The Pauli labels and literal matrices are those of StabilizerPairLocalUnitaryInequivalence: I, X, Y = i X Z, and Z. Only the real signs plus and minus are allowed, so these operators are Hermitian. The Kronecker product acts on the same two computational indices.

**Definition 1.3 (Two independent commuting generators).**

$$\forall psi \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C},\; (\operatorname{PureStabilizer}\left(psi\right)) \Leftrightarrow ((\operatorname{unitVector}\left(psi\right)) \land (\exists P \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \exists Q \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{IsHermitianPauli}\left(P\right)) \land ((\operatorname{IsHermitianPauli}\left(Q\right)) \land ((P \ne 1) \land ((P \ne -(1)) \land ((Q \ne 1) \land ((Q \ne -(1)) \land ((Q \ne P) \land ((Q \ne -(P)) \land ((P \cdot Q = Q \cdot P) \land ((\operatorname{Matrix.mulVec}\left(P, psi\right) = psi) \land (\operatorname{Matrix.mulVec}\left(Q, psi\right) = psi))))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.PureStabilizer` (`✓ std3`).

*Citation.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

A two-qubit pure stabilizer vector is normalized and fixed by two commuting signed Hermitian Pauli matrices. Each generator differs from both signs of the identity, and the second differs from both signs of the first. These conditions express two independent nontrivial stabilizer generators.

**Definition 1.4 (The full convex stabilizer hull).**

$$\operatorname{STAB} = \operatorname{convexHull}\left(\mathbb{R}, \{A:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right) \mid \exists psi \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C},\; (\operatorname{PureStabilizer}\left(psi\right)) \land (A = \operatorname{rankOneDensity}\left(psi\right))\}\right)$$

*Formalization.* `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.STAB` (`✓ std3`).

*Citation.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

Appendix F, PDF p. 8, preceding equation (F2), verbatim: “while STAB is defined as the convex hull of pure stabilizer states:” The equation is STAB := {ρ | ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|}, followed by “where ψᵢ are pure stabilizer states.” convexHull over the real numbers encodes all finite probability mixtures. PureStateHandshake.rankOneDensity is literally Matrix.vecMulVec(psi,star(psi)). STAB includes mixtures drawn from different stabilizer bases.

**Definition 1.5 (The common product unitary).**

$$\forall UA \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall UB \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{localMatrix}\left(UA, UB\right) = \operatorname{Matrix.kronecker}\left(\operatorname{val}\left(UA\right), \operatorname{val}\left(UB\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.localMatrix` (`✓ std3`).

*Citation.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

The two matrices belong to Matrix.unitaryGroup(Fin(2),C). val exposes their matrices, and their Kronecker product is the unitary on the joint system.

**Definition 1.6 (Local-unitary conjugation).**

$$\forall UA \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall UB \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \operatorname{localAction}\left(UA, UB, rho\right) = \operatorname{localMatrix}\left(UA, UB\right) \cdot rho \cdot \operatorname{conjTranspose}\left(\operatorname{localMatrix}\left(UA, UB\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.localAction` (`✓ std3`).

*Citation.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

The same pair of local unitaries acts on the entire density matrix. conjTranspose is the complex matrix adjoint.

**Definition 1.7 (Pure product-state projectors).**

$$\operatorname{ProductPureProjectors} = \{A:\operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right) \mid \exists a \in \operatorname{Fin}\left(2\right) \to \mathbb{C},\; \exists b \in \operatorname{Fin}\left(2\right) \to \mathbb{C},\; (\operatorname{unitVector}\left(a\right)) \land ((\operatorname{unitVector}\left(b\right)) \land (A = \operatorname{rankOneDensity}\left(\operatorname{productVector}\left(a, b\right)\right)))\}$$

*Formalization.* `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.ProductPureProjectors` (`✓ std3`).

*Citation.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

Both local vectors are normalized. FiniteLocalLatitudeGeometry.productVector supplies their literal product amplitude a(i) b(j), which is projected by the existing rankOneDensity construction, giving the tensor product of the two local rank-one density matrices.

**Definition 1.8 (Separable mixed states).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{Separable}\left(rho\right)) \Leftrightarrow (rho \in \operatorname{convexHull}\left(\mathbb{R}, \operatorname{ProductPureProjectors}\right))$$

*Formalization.* `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.Separable` (`✓ std3`).

*Citation.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

Appendix F, PDF p. 8, preceding equation (F1), verbatim: “A separable state is defined as the convex hull of pure product states [1]:” The real convex hull allows every finite ensemble of normalized product-state projectors.

**Definition 1.9 (Qian–Wang's separable-state conjecture).**

$$(\operatorname{claim}) \Leftrightarrow (\exists rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{IsDensity}\left(rho\right)) \land ((\operatorname{Separable}\left(rho\right)) \land (\forall UA \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall UB \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \neg (\operatorname{localAction}\left(UA, UB, rho\right) \in \operatorname{STAB}))))$$

*Formalization.* `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.claim` (`✓ std3`).

*Citation.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

Appendix F, PDF p. 8, verbatim: “However, we are unaware of any proof guaranteeing that every separable multi-qubit state can be transformed into a state belonging to STAB using only local unitary transformations, and we conjecture that this is not the case.” The existential two-qubit density matrix rho is positive semidefinite with trace one, as expressed by StructuredNegativityCoincidenceRefutation.IsDensity. Its separability is the literal convex-product-ensemble condition. The universal quantifier ranges independently over all pairs of single-qubit unitaries. A two-qubit example proves the source's existential multi-qubit assertion.

**Theorem 1.10 (An infinite family proves the conjecture).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dongheng Qian; Jing Wang (2025). *Quantum non-local nonstabilizerness*. DOI: [10.1103/PhysRevA.111.052443](https://doi.org/10.1103/PhysRevA.111.052443). URL: <https://arxiv.org/abs/2502.06393v4>.

*Commentary.*

For every real p,c,s with 0 < p < 1, c > 0, s > 0, c² + s² = 1 and c² ≠ 1/2, put b = (c,s) and rho = p |00⟩⟨00| + (1-p) |bb⟩⟨bb|. This is a density matrix and an explicit convex mixture of product pure states, yet no local-unitary conjugate belongs to STAB. Choose p = 1/2, c = 3/5 and s = 4/5 for the existential conclusion. Every positive-weight vector in any pulled-back stabilizer ensemble lies in span{u,v}, where u = |00⟩ and v = |bb⟩. Its only product rays are u and v; its only maximally entangled ray has coefficients alpha = -beta, namely (v-u)/(sqrt(2)s) after normalization. Stabilizer classification and positivity eliminate that entangled ray from the ensemble, forcing both product rays to occur. Their common local unitary preserves the single-qubit squared overlap c², whereas Pauli eigenprojectors have overlap spectrum {0,1/2,1}. The stated parameter conditions exclude all three values. This argument uses product-vector and maximal-entanglement invariance under local unitaries; the Pauli restriction enters after stabilizer classification.

## References

- Truth anchor: `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.IsHermitianPauli`
- Truth anchor: `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.ProductPureProjectors`
- Truth anchor: `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.PureStabilizer`
- Truth anchor: `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.STAB`
- Truth anchor: `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.Separable`
- Truth anchor: `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.claim`
- Truth anchor: `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.localAction`
- Truth anchor: `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.localMatrix`
- Truth anchor: `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.result`
- Truth anchor: `D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.unitVector`
- Dependency: [D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation](../Entanglement/StructuredNegativityCoincidenceRefutation.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Information/SignedPauliSumNormRefutation](SignedPauliSumNormRefutation.md)
- Dependency: [D5/S3/Quantum/Magic/WignerDistanceMinimum](../Magic/WignerDistanceMinimum.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/Quantum/Recovery/FiniteLocalLatitudeGeometry](../Recovery/FiniteLocalLatitudeGeometry.md)
