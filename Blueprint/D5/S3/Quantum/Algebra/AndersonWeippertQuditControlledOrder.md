# Controlled qudit gates have prime-power target order

## Abstract

A controlled qudit gate in the Clifford hierarchy has prime-power target order.

**Definition 1.1 (Control in computational block one).**

$$\forall p: \mathbb{N}, [\operatorname{NeZero}\left(p\right)], \forall n: \mathbb{N}, \forall U: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right), \forall i: (\operatorname{Fin}\left(n + 1\right) \to \operatorname{ZMod}\left(p\right)), \forall j: (\operatorname{Fin}\left(n + 1\right) \to \operatorname{ZMod}\left(p\right)), \operatorname{controlled}\left(p, U, i, j\right) = \operatorname{ite}\left(i(0) = j(0), \operatorname{ite}\left(i(0) = 1, U(\operatorname{Fin}.\operatorname{tail}(i), \operatorname{Fin}.\operatorname{tail}(j)), (1: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right))(\operatorname{Fin}.\operatorname{tail}(i), \operatorname{Fin}.\operatorname{tail}(j))\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/AndersonWeippertQuditControlledOrder.controlled` (`✓ std3`).

*Citation.* J. T. Anderson and M. Weippert (2024). *Controlled Gates in the Clifford Hierarchy*. DOI: [10.48550/arXiv.2410.04711](https://doi.org/10.48550/arXiv.2410.04711). URL: <https://arxiv.org/abs/2410.04711v3>.

*Commentary.*

Section 1.1, p. 2: "We will write C(U) = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U where the control is on the left side of the tensor product.". In prime dimension p, the matrix has U in control block one and the identity in every other block. Coordinate zero is the control; Fin.tail gives the n target coordinates.

**Definition 1.2 (The controlled-qudit order conjecture).**

$$claim = (\forall p: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}(p)) \Rightarrow \forall n: \mathbb{N}, \forall U: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right), (U \in \operatorname{Matrix}.\operatorname{unitaryGroup}((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C})) \Rightarrow (\exists k: \mathbb{N}, \operatorname{controlled}\left(p, U\right) \in \operatorname{cliffordHierarchy}\left(p, n + 1, k\right)) \Rightarrow \exists m: \mathbb{N}, \operatorname{orderOf}\left(U\right) = p^{m})$$

*Formalization.* `D5/S3/Quantum/Algebra/AndersonWeippertQuditControlledOrder.claim` (`✓ std3`).

*Citation.* J. T. Anderson and M. Weippert (2024). *Controlled Gates in the Clifford Hierarchy*. DOI: [10.48550/arXiv.2410.04711](https://doi.org/10.48550/arXiv.2410.04711). URL: <https://arxiv.org/abs/2410.04711v3>.

*Commentary.*

Section 4, p. 7: "It is tempting to conjecture for the qudit case that C(U) is in the Clifford Hierarchy only if U is order d^m where d is the local qudit dimension and m is a non-negative integer. We leave this as an open problem." Here d is the prime p, basis indices are functions from Fin n to ZMod p, and n ranges over all natural numbers, including zero. The phase group of the Pauli operators is the unit circle. The primality hypothesis supplies NeZero p. The existential hierarchy index is finite, and orderOf is the exact multiplicative matrix order.

**Theorem 1.3 (The exact target order is a power of the local prime).**

$$\forall p: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}(p)) \Rightarrow \forall n: \mathbb{N}, \forall U: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C}\right), (U \in \operatorname{Matrix}.\operatorname{unitaryGroup}((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), \mathbb{C})) \Rightarrow (\exists k: \mathbb{N}, \operatorname{controlled}\left(p, U\right) \in \operatorname{cliffordHierarchy}\left(p, n + 1, k\right)) \Rightarrow \exists m: \mathbb{N}, \operatorname{orderOf}\left(U\right) = p^{m}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AndersonWeippertQuditControlledOrder.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. T. Anderson and M. Weippert (2024). *Controlled Gates in the Clifford Hierarchy*. DOI: [10.48550/arXiv.2410.04711](https://doi.org/10.48550/arXiv.2410.04711). URL: <https://arxiv.org/abs/2410.04711v3>.

*Commentary.*

Repeated commutators with the control shift reach the identity. On the controlled blocks, each commutator takes a cyclic difference of the integer power exponents. Their positive content is a power of p, and the exact order of U divides that content. Thus the conclusion includes the global phase. The converse and the least hierarchy level are not asserted.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/AndersonWeippertQuditControlledOrder.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/AndersonWeippertQuditControlledOrder.controlled`
- Truth anchor: `D5/S3/Quantum/Algebra/AndersonWeippertQuditControlledOrder.result`
- Dependency: [D5/S3/Arith/Primes/CyclicDifferencePrimeContent](../../Arith/Primes/CyclicDifferencePrimeContent.md)
- Dependency: [D5/S3/Observer/WindowRegister](../../Observer/WindowRegister.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylCliffordDescent](WeylCliffordDescent.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacement](WeylDisplacement.md)
- Dependency: [D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank](../Codes/StabilizerGenuineEntanglementCommutationRank.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../Recovery/PurifiedLocalPath.md)
