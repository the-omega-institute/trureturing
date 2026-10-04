# Dicke states cannot become total products under Clifford gates

## Abstract

No n-qubit Clifford maps a nontrivial Dicke state to a total product of normalized single-qubit states when n > 2. A Pauli count and a common-denominator obstruction prove Remark F.1 of Borda Kuhlmann and Rincón.

**Definition 1.1 (Remark F.1).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; ((2 < n) \land ((0 < k) \land (k < n))) \Rightarrow (\forall U \in \operatorname{Operator}\left(n\right),\; (U \in \operatorname{Clifford}\left(n\right)) \Rightarrow (\forall phi \in \operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(2\right) \to \mathbb{C}),\; (\forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{UnitSpinor}\left(phi\left(j\right)\right)) \Rightarrow (\operatorname{mulVec}\left(U, \operatorname{dicke}\left(n, k\right)\right) \ne \operatorname{productVector}\left(phi\right)))))$$

*Formalization.* `D5/S3/Quantum/Information/DickeCliffordProductObstruction.claim` (`✓ std3`).

*Citation.* A. Borda Kuhlmann; J. Rincón (2026). *Magic-protected entanglement and Clifford-irreducible structure in magic state space*. DOI: [10.48550/arXiv.2607.18400](https://doi.org/10.48550/arXiv.2607.18400). URL: <https://arxiv.org/abs/2607.18400v1>.

*Commentary.*

Page 16, Remark F.1: "(Dicke states and the fundamental property of W-magic). Let |ψ⟩ = |D^n_k⟩ be a nontrivial Dicke state, with 0 < k < n and n > 2, and let C ∈ C_n be an arbitrary n-qubit Clifford gate. Then, for any total product state |ϕ_1⟩ ⊗ · · · ⊗ |ϕ_n⟩, C|ψ⟩ ≠ ⊗_{j=1}^{n} |ϕ_j⟩. That is, nontrivial Dicke states are expected to exhibit the fundamental property of W-magic in Definition V.1." The encoding uses n,k in Nat, bitstrings Fin n -> Fin 2, the source's special-unitary normalizer, and arbitrary locally normalized complex amplitudes phi(j). The symbols U and phi encode C and the local kets. The inequality is equality of full vectors, with no restriction on the local phases.

**Theorem 1.2 (The product obstruction).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; ((2 < n) \land ((0 < k) \land (k < n))) \Rightarrow (\forall U \in \operatorname{Operator}\left(n\right),\; (U \in \operatorname{Clifford}\left(n\right)) \Rightarrow (\forall phi \in \operatorname{Fin}\left(n\right) \to (\operatorname{Fin}\left(2\right) \to \mathbb{C}),\; (\forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{UnitSpinor}\left(phi\left(j\right)\right)) \Rightarrow (\operatorname{mulVec}\left(U, \operatorname{dicke}\left(n, k\right)\right) \ne \operatorname{productVector}\left(phi\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DickeCliffordProductObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Borda Kuhlmann; J. Rincón (2026). *Magic-protected entanglement and Clifford-irreducible structure in magic state space*. DOI: [10.48550/arXiv.2607.18400](https://doi.org/10.48550/arXiv.2607.18400). URL: <https://arxiv.org/abs/2607.18400v1>.

*Commentary.*

Clifford conjugation permutes Hermitian Pauli words up to sign. It preserves both the number of unit-modulus expectations and integrality after multiplication by a common denominator B. The Dicke certificate bounds that count by two, or four if n = 2k, and gives B = n.choose k. For a normalized product whose Pauli expectations become integers after multiplication by the positive common denominator B, each local Bloch vector is rational. Reducing its integer coordinates with their positive denominator d gives a primitive vector satisfying a^2+b^2+c^2=d^2. Denominator two is impossible, and denominator one gives a Pauli eigenstate. Tensoring Bezout identities shows that the product of the local denominators divides B. If s of them equal one, choosing the identity or a local unit-expectation Pauli at each of those sites gives at least 2^s unit-expectation words, while the denominator product is at least 3^(n-s). Thus s <= 2. For n >= 4, the inductive estimate n.choose k < 3^(n-2) contradicts these simultaneous bounds. For n = 3 the layer is unbalanced, hence s <= 1 and 9 <= B <= 3 is impossible. This proves the total-product assertion, including balanced Dicke states and three-qubit W states; it makes no assertion about disentangling across a single bipartition.

## References

- Truth anchor: `D5/S3/Quantum/Information/DickeCliffordProductObstruction.claim`
- Truth anchor: `D5/S3/Quantum/Information/DickeCliffordProductObstruction.result`
- Dependency: [D5/S3/Quantum/Information/DickeClifford/DickeCertificate](DickeClifford/DickeCertificate.md)
- Dependency: [D5/S3/Quantum/Recovery/FiniteLocalLatitudeGeometry](../Recovery/FiniteLocalLatitudeGeometry.md)
