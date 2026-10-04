# A Pauli certificate for Dicke states

## Abstract

For every nontrivial Dicke state with more than two qubits, all Pauli expectations have binomial common denominator, and at most two Hermitian Pauli words have unit-modulus expectation, or at most four on the balanced layer.

**Definition 1.1 (Pauli matrices with phases).**

$$\forall n \in \mathbb{N},\; \operatorname{pauliMatrices}\left(n\right) = \left\{\operatorname{val}\left(u\right) \mid u \in \operatorname{pauliGroup}\left(n\right)\right\}$$

*Formalization.* `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.pauliMatrices` (`✓ std3`).

*Citation.* A. Borda Kuhlmann; J. Rincón (2026). *Magic-protected entanglement and Clifford-irreducible structure in magic state space*. DOI: [10.48550/arXiv.2607.18400](https://doi.org/10.48550/arXiv.2607.18400). URL: <https://arxiv.org/abs/2607.18400v1>.

*Commentary.*

The existing n-qubit Pauli subgroup is represented in the matrix algebra through the value map on units. Its matrices are i^c times a tensor product of I, X, Y and Z, with c in Fin 4. The reused State(n) is (Fin n -> Fin 2) -> C, and Operator(n) is the square complex matrix algebra indexed by those bitstrings.

**Definition 1.2 (Clifford normalizer).**

$$\forall n \in \mathbb{N},\; \forall U \in \operatorname{Operator}\left(n\right),\; U \in \operatorname{Clifford}\left(n\right) \Leftrightarrow ((U \in \operatorname{specialUnitaryGroup}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right)) \land (\forall P \in \operatorname{Operator}\left(n\right),\; (P \in \operatorname{pauliMatrices}\left(n\right)) \Rightarrow (U \cdot P \cdot \operatorname{conjTranspose}\left(U\right) \in \operatorname{pauliMatrices}\left(n\right))))$$

*Formalization.* `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.Clifford` (`✓ std3`).

*Citation.* A. Borda Kuhlmann; J. Rincón (2026). *Magic-protected entanglement and Clifford-irreducible structure in magic state space*. DOI: [10.48550/arXiv.2607.18400](https://doi.org/10.48550/arXiv.2607.18400). URL: <https://arxiv.org/abs/2607.18400v1>.

*Commentary.*

Page 11, Definition A.1: "The n-qubit Clifford group is defined as the normalizer of the n-qubit Pauli group (P_n) in SU(2^n), C_n := N_{SU(2^n)}(P_n): C_n := {U ∈ SU(2^n) : U P U† ∈ P_n, ∀P ∈ P_n}." The carrier Fin n -> Fin 2 has cardinality 2^n. Conjugate transpose encodes the dagger, and specialUnitaryGroup requires unitarity and determinant one.

**Definition 1.3 (Normalized Dicke vector).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right),\; \operatorname{dicke}\left(n, k, x\right) = \operatorname{ite}\left(\operatorname{hammingNorm}\left(x\right) = k, \operatorname{asComplex}\left(\operatorname{inv}\left(\operatorname{sqrt}\left(\operatorname{asReal}\left(\operatorname{choose}\left(n, k\right)\right)\right)\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.dicke` (`✓ std3`).

*Citation.* A. Borda Kuhlmann; J. Rincón (2026). *Magic-protected entanglement and Clifford-irreducible structure in magic state space*. DOI: [10.48550/arXiv.2607.18400](https://doi.org/10.48550/arXiv.2607.18400). URL: <https://arxiv.org/abs/2607.18400v1>.

*Commentary.*

Page 16, Appendix F.2: "Dicke states are defined as [46, 47] |D^n_k⟩ = (1/√(n choose k)) Σ_{w(x)=k} |x⟩, where w(x) is the Hamming weight of the bitstring x." The imported Mathlib hammingNorm counts the nonzero bits, which is the Hamming weight on Fin 2. Qubits are indexed from zero by Fin n. In the computational basis this has amplitude the complex cast of the reciprocal real square root of n.choose k on weight k, and zero elsewhere.

**Definition 1.4 (Total product vector).**

$$\forall n \in \mathbb{N},\; \forall phi \in \operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(2\right) \to \mathbb{C}),\; \forall x \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right),\; \operatorname{productVector}\left(phi, x\right) = \prod_{j:\operatorname{Fin}\left(n\right)}(phi\left(j, x\left(j\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.productVector` (`✓ std3`).

*Citation.* A. Borda Kuhlmann; J. Rincón (2026). *Magic-protected entanglement and Clifford-irreducible structure in magic state space*. DOI: [10.48550/arXiv.2607.18400](https://doi.org/10.48550/arXiv.2607.18400). URL: <https://arxiv.org/abs/2607.18400v1>.

*Commentary.*

The amplitude of the total product at a bitstring x is the product of the local amplitudes phi(j)(x(j)).

Local normalization uses the frozen UnitSpinor definition from `D5/S3/Quantum/Recovery/FiniteLocalLatitudeGeometry.UnitSpinor`. It is the unit-norm condition on C^2: $\forall phi \in \operatorname{Fin}\left(2\right) \to \mathbb{C},\; \operatorname{UnitSpinor}\left(phi\right) \Leftrightarrow (\sum_{b:\operatorname{Fin}\left(2\right)}(\operatorname{normSq}\left(phi\left(b\right)\right)) = 1)$

**Definition 1.5 (Pauli expectation).**

$$\forall n \in \mathbb{N},\; \forall psi \in \operatorname{State}\left(n\right),\; \forall P \in \operatorname{Operator}\left(n\right),\; \operatorname{expectation}\left(psi, P\right) = \operatorname{dotProduct}\left(\operatorname{star}\left(psi\right), \operatorname{mulVec}\left(P, psi\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.expectation` (`✓ std3`).

*Citation.* A. Borda Kuhlmann; J. Rincón (2026). *Magic-protected entanglement and Clifford-irreducible structure in magic state space*. DOI: [10.48550/arXiv.2607.18400](https://doi.org/10.48550/arXiv.2607.18400). URL: <https://arxiv.org/abs/2607.18400v1>.

*Commentary.*

The complex expectation is the dot product of the conjugated state and the matrix acting on the state. star acts pointwise on state coefficients, and mulVec is matrix-vector multiplication.

**Definition 1.6 (Number of unit-modulus expectations).**

$$\forall n \in \mathbb{N},\; \forall psi \in \operatorname{State}\left(n\right),\; \operatorname{pauliUnitCount}\left(psi\right) = \operatorname{card}\left(\{p:\operatorname{Fin}\left(n\right) \to Pauli \mid \left\lVert \operatorname{expectation}\left(psi, \operatorname{wordOp}\left(p\right)\right) \right\rVert = 1\}\right)$$

*Formalization.* `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.pauliUnitCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Borda Kuhlmann; J. Rincón (2026). *Magic-protected entanglement and Clifford-irreducible structure in magic state space*. DOI: [10.48550/arXiv.2607.18400](https://doi.org/10.48550/arXiv.2607.18400). URL: <https://arxiv.org/abs/2607.18400v1>.

*Commentary.*

Count each Hermitian Pauli word in {I,X,Y,Z}^n once, including the identity and excluding scalar phase copies. The count selects exactly the expectations whose complex norm is one.

**Definition 1.7 (Integral scaled expectations).**

$$\forall n \in \mathbb{N},\; \forall B \in \mathbb{N},\; \forall psi \in \operatorname{State}\left(n\right),\; \operatorname{HasIntegerPauliDenominator}\left(B, psi\right) \Leftrightarrow (\forall p \in \operatorname{Fin}\left(n\right) \to Pauli,\; \exists a \in \mathbb{Z},\; \operatorname{asComplex}\left(B\right) \cdot \operatorname{expectation}\left(psi, \operatorname{wordOp}\left(p\right)\right) = \operatorname{asComplex}\left(a\right))$$

*Formalization.* `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.HasIntegerPauliDenominator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Borda Kuhlmann; J. Rincón (2026). *Magic-protected entanglement and Clifford-irreducible structure in magic state space*. DOI: [10.48550/arXiv.2607.18400](https://doi.org/10.48550/arXiv.2607.18400). URL: <https://arxiv.org/abs/2607.18400v1>.

*Commentary.*

All expectations, multiplied by the natural number B cast into C, are integer casts. This asserts that B is a common denominator; it makes no least-denominator assertion.

**Theorem 1.8 (Dicke denominator and unit count).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; ((2 < n) \land ((0 < k) \land (k < n))) \Rightarrow ((\operatorname{HasIntegerPauliDenominator}\left(\operatorname{choose}\left(n, k\right), \operatorname{dicke}\left(n, k\right)\right)) \land (\operatorname{pauliUnitCount}\left(\operatorname{dicke}\left(n, k\right)\right) \le \operatorname{ite}\left(n = 2 \cdot k, 4, 2\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.dicke_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Borda Kuhlmann; J. Rincón (2026). *Magic-protected entanglement and Clifford-irreducible structure in magic state space*. DOI: [10.48550/arXiv.2607.18400](https://doi.org/10.48550/arXiv.2607.18400). URL: <https://arxiv.org/abs/2607.18400v1>.

*Commentary.*

A Pauli word acts by a bit flip and a phase. A unit-modulus expectation means that the normalized state is an eigenvector. Exchanging one selected and one unselected bit in the weight-k layer forces every flip bit to agree and every sign bit to agree. Therefore only the identity and the all-Z word can occur, with the all-X and all-Y words also possible when n = 2k. Counting this list gives the stated upper bounds, without claiming equality. The unnormalized weight-layer indicator has squared norm n.choose k. Its expectations are Gaussian integers; Hermiticity makes them real integers, so multiplication of a normalized expectation by n.choose k is an integer. Both invariants concern the same Dicke vector.

## References

- Truth anchor: `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.Clifford`
- Truth anchor: `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.HasIntegerPauliDenominator`
- Truth anchor: `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.dicke`
- Truth anchor: `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.dicke_certificate`
- Truth anchor: `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.expectation`
- Truth anchor: `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.pauliMatrices`
- Truth anchor: `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.pauliUnitCount`
- Truth anchor: `D5/S3/Quantum/Information/DickeClifford/DickeCertificate.productVector`
- Truth anchor: `D5/S3/Quantum/Recovery/FiniteLocalLatitudeGeometry.UnitSpinor`
- Dependency: [D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence](../StabilizerPairLocalUnitaryInequivalence.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
