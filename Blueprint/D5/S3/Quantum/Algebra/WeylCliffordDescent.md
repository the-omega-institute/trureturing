# Termination of Pauli commutators in the Clifford hierarchy

## Abstract

Repeated commutators with a Pauli terminate in the Clifford hierarchy.

**Definition 1.1 (Pauli operators with unit-modulus phase).**

$$\forall p: \mathbb{N}, [\operatorname{NeZero}\left(p\right)], \forall n: \mathbb{N}, \operatorname{pauli}\left(p, n\right) = \{A: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right) \mid \exists c: \mathbb{C}, \exists a: (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \exists b: (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), (\Vert c \Vert = 1) \land (A = \operatorname{SMul}.\operatorname{smul}(c, \operatorname{ProductPrefixRigidity}.\operatorname{productMap}(\lambda _: \operatorname{Fin}\left(n\right) \mapsto \operatorname{ZMod}\left(p\right), \lambda k: \operatorname{Fin}\left(n\right) \mapsto \operatorname{displacement}\left(p, a(k), b(k)\right))))\}$$

*Formalization.* `D5/S3/Quantum/Algebra/WeylCliffordDescent.pauli` (`✓ std3`).

*Citation.* J. T. Anderson and M. Weippert (2024). *Controlled Gates in the Clifford Hierarchy*. DOI: [10.48550/arXiv.2410.04711](https://doi.org/10.48550/arXiv.2410.04711). URL: <https://arxiv.org/abs/2410.04711v3>.

*Commentary.*

Section 2, p. 2: "The elements form a group and consist of Pauli strings i.e. tensor products of single-qubit Pauli matrices times a U (1) phase (usually restricted to i^k or ±1). The details of this phase are not important here and any of these definitions of CH1 will suffice for our proofs below." The complex scalar has norm one, and the Weyl labels range independently over all coordinates.

**Definition 1.2 (The finite Clifford hierarchy).**

$$\begin{aligned}\forall p: \mathbb{N}, [\operatorname{NeZero}\left(p\right)], \forall n: \mathbb{N}, \operatorname{cliffordHierarchy}\left(p, n, 0\right) = \emptyset\\\forall p: \mathbb{N}, [\operatorname{NeZero}\left(p\right)], \forall n: \mathbb{N}, \operatorname{cliffordHierarchy}\left(p, n, 1\right) = \operatorname{pauli}\left(p, n\right)\\\forall p: \mathbb{N}, [\operatorname{NeZero}\left(p\right)], \forall n: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{cliffordHierarchy}\left(p, n, k + 2\right) = \{V: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right) \mid (V \in \operatorname{Matrix}.\operatorname{unitaryGroup}((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C})) \land (\forall P: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right), (P \in \operatorname{pauli}\left(p, n\right)) \Rightarrow V \cdot P \cdot \operatorname{star}\left(V\right) \in \operatorname{cliffordHierarchy}\left(p, n, k + 1\right))\}\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Algebra/WeylCliffordDescent.cliffordHierarchy` (`✓ std3`).

*Citation.* J. T. Anderson and M. Weippert (2024). *Controlled Gates in the Clifford Hierarchy*. DOI: [10.48550/arXiv.2410.04711](https://doi.org/10.48550/arXiv.2410.04711). URL: <https://arxiv.org/abs/2410.04711v3>.

*Commentary.*

Equation (1), p. 1: "The n-qubit Clifford Hierarchy [1, 7] is recursively defined as CHk ≡ {U |U P U † ⊆ CHk−1 , ∀P ∈ Pn } with the first level (k = 1) defined as CH1 ≡ Pn , the n-qubit Pauli group." The formulas use prime-dimensional Weyl operators. Level zero is empty; levels at least two require unitarity.

**Definition 1.3 (A star commutator).**

$$\forall p: \mathbb{N}, [\operatorname{NeZero}\left(p\right)], \forall n: \mathbb{N}, \forall V: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right), \forall Q: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right), \operatorname{commutator}\left(V, Q\right) = V \cdot Q \cdot \operatorname{star}\left(V\right) \cdot \operatorname{star}\left(Q\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/WeylCliffordDescent.commutator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The expression is defined for arbitrary square matrices. On unitary matrices it is the multiplicative group commutator.

**Theorem 1.4 (Commutators with a Pauli reach the identity).**

$$\forall p: \mathbb{N}, [\operatorname{NeZero}\left(p\right)], \forall n: \mathbb{N}, \forall V: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right), \forall Q: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right), \forall k: \mathbb{N}, (V \in \operatorname{cliffordHierarchy}\left(p, n, k\right)) \Rightarrow (Q \in \operatorname{pauli}\left(p, n\right)) \Rightarrow \operatorname{Function}.\operatorname{iterate}(\lambda A: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right) \mapsto \operatorname{commutator}\left(A, Q\right), k + 1, V) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylCliffordDescent.hierarchy_terminates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. T. Anderson and M. Weippert (2024). *Controlled Gates in the Clifford Hierarchy*. DOI: [10.48550/arXiv.2410.04711](https://doi.org/10.48550/arXiv.2410.04711). URL: <https://arxiv.org/abs/2410.04711v3>.

*Commentary.*

If V is in level k and Q is Pauli, k plus one repeated commutators give the identity. Right multiplication by a Pauli preserves each level, a Pauli commutator is scalar, and the next commutator of that scalar is the identity.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/WeylCliffordDescent.cliffordHierarchy`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylCliffordDescent.commutator`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylCliffordDescent.hierarchy_terminates`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylCliffordDescent.pauli`
- Dependency: [D5/S3/Observer/WindowRegister](../../Observer/WindowRegister.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacement](WeylDisplacement.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementAdjoint](WeylDisplacementAdjoint.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementConjugation](WeylDisplacementConjugation.md)
- Dependency: [D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank](../Codes/StabilizerGenuineEntanglementCommutationRank.md)
- Dependency: [D5/S3/Quantum/Magic/SubspaceStabilizerEntropy](../Magic/SubspaceStabilizerEntropy.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../Recovery/PurifiedLocalPath.md)
- Dependency: [D5/S3/QuantumBounds/NonlocalityDepthQuantumBound](../../QuantumBounds/NonlocalityDepthQuantumBound.md)
