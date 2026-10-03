# Tensor rules for the qubit Wigner distance

## Abstract

Using the compact minimum bridge in WignerDistanceMinimum, equatorial qubit states obey exact multiplicativity of one plus the Wigner distance. Nonpositive Bloch-product states obey self-tensor superadditivity.

**Definition 1.1 (Pauli expectation coordinates).**

$$\forall rho \in QubitMatrix,\; \forall p \in Pauli,\; \operatorname{bloch}\left(rho, p\right) = \operatorname{re}\left(\operatorname{trace}\left(rho \cdot \operatorname{pauliMatrix}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.bloch` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

bloch(rho,p) is the real part of tr(rho pauliMatrix(p)). For p = X,Y,Z these are the Bloch coordinates r_x,r_y,r_z. Page 7: "For a single-qubit state ρ with Bloch vector r⃗, write s(ρ) := sgn(r_x r_y r_z)." The nonpositive sign condition is exactly r_x r_y r_z ≤ 0.

**Definition 1.2 (Conjecture 5.6).**

$$(claimEquatorial) \Leftrightarrow (\forall rho \in QubitMatrix,\; \forall sigma \in QubitMatrix,\; (\operatorname{IsDensity}\left(rho\right)) \Rightarrow ((\operatorname{IsDensity}\left(sigma\right)) \Rightarrow ((\operatorname{bloch}\left(rho, Z\right) = 0) \Rightarrow ((\operatorname{bloch}\left(sigma, Z\right) = 0) \Rightarrow (\operatorname{CTwo}\left(\operatorname{kronecker}\left(rho, sigma\right)\right) = \operatorname{COne}\left(rho\right) + \operatorname{COne}\left(sigma\right) + \operatorname{COne}\left(rho\right) \cdot \operatorname{COne}\left(sigma\right))))))$$

*Formalization.* `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.claimEquatorial` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Page 8, Conjecture 5.6 (Equatorial multiplicativity): "For ⟨Z⟩_ρ = ⟨Z⟩_σ = 0: C(ρ ⊗ σ) = C(ρ) + C(σ) + C(ρ)C(σ)." The quantifiers range over every complex two-by-two density matrix rho and sigma. IsDensity means positive semidefinite with trace one; the two Z expectations vanish separately. COne and CTwo denote WignerDistanceMinimum.COne and WignerDistanceMinimum.CTwo; COne_min and CTwo_min identify them with the source minimum on the corresponding Hilbert spaces.

**Definition 1.3 (Conjecture 5.7).**

$$(claimSelfTensor) \Leftrightarrow (\forall rho \in QubitMatrix,\; (\operatorname{IsDensity}\left(rho\right)) \Rightarrow ((\operatorname{bloch}\left(rho, X\right) \cdot \operatorname{bloch}\left(rho, Y\right) \cdot \operatorname{bloch}\left(rho, Z\right) \le 0) \Rightarrow (\operatorname{CTwo}\left(\operatorname{kronecker}\left(rho, rho\right)\right) \ge 2 \cdot \operatorname{COne}\left(rho\right))))$$

*Formalization.* `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.claimSelfTensor` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Page 8, Conjecture 5.7 (Self-tensor superadditivity, s ≤ 0 branch): "For any qubit state ρ with s(ρ)≤ 0: C(ρ ⊗ ρ) ≥ 2C(ρ)." Every density matrix is included, with the sign condition encoded by bloch(rho,X) bloch(rho,Y) bloch(rho,Z) ≤ 0. This includes zero coordinates and the stabilizer boundary.

**Theorem 1.4 (Equatorial multiplicativity holds).**

$$claimEquatorial$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultEquatorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Every qubit Wigner vector has at most one negative coordinate. On the nonpositive Bloch-product branch an explicit stabilizer-edge mixture has error ‖W‖₁−1. A product sign functional is bounded by one on every actual two-qubit stabilizer, using subgroup generators and an exact rational certificate on sixty candidate vectors. Convex weak duality gives the lower bound ‖W_rho‖₁ ‖W_sigma‖₁−1. The product of the two nearest mixtures gives the matching upper bound. Equatorial states lie on the zero Bloch-product branch.

**Theorem 1.5 (Self-tensor superadditivity holds).**

$$claimSelfTensor$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultSelfTensor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

On the nonpositive branch COne(rho) = ‖W_rho‖₁−1. Applying the same product dual bound to two copies of rho gives at least (1+COne(rho))²−1, which is at least 2 COne(rho). The free tensor mixture establishes nonemptiness of the two-qubit free set.

## References

- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.bloch`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.claimEquatorial`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.claimSelfTensor`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultEquatorial`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultSelfTensor`
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence](../Information/BinaryStabilizerLocalInequivalence.md)
- Dependency: [D5/S3/Quantum/Magic/WignerDistanceMinimum](WignerDistanceMinimum.md)
- Dependency: [D5/S3/Quantum/Magic/WignerSimplexNearestEdge](WignerSimplexNearestEdge.md)
- Dependency: [D5/S3/QuantumBounds/CHSHWitness](../../QuantumBounds/CHSHWitness.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](../../QuantumChannels/CoPRelativeQuantumnessRefutation.md)
