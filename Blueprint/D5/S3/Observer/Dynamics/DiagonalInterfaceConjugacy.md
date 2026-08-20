# Diagonal Interface Conjugacy

## Abstract

Diagonal-interface-preserving similarity exactly recovers finite map conjugacy.

**Theorem 1.1 (Diagonal-interface similarity is map conjugacy).**

$$\forall Y, Z: \operatorname{Type},\ [\operatorname{Finite}(Y)], [\operatorname{Finite}(Z)],\ tau: Y \to Y, sigma: Z \to Z,\\(\exists phi: \operatorname{Equiv}(Y, Z), \forall y, phi(tau(y)) = sigma(phi(y))) \iff \\\exists U: \operatorname{LinearEquiv}(\mathbb{C}, \operatorname{Finsupp}(Y, \mathbb{C}), \operatorname{Finsupp}(Z, \mathbb{C})),\ U.conj(transferOperator(tau)) = transferOperator(sigma) \land\\\operatorname{image}(U.conj, diagonalInterface(Y)) = diagonalInterface(Z).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Dynamics/DiagonalInterfaceConjugacy.diagonal_interface_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each finite state type, the transfer operator is constructed from the state map by sending every coordinate basis vector to the basis vector at its image. The diagonal interface is independently constructed as the full range of pointwise multiplication operators.

A state equivalence transports coordinate functions and directly conjugates both constructions. Conversely, diagonal preservation makes each conjugated coordinate projection diagonal. Its nonzero coordinate reconstructs an injective state map, and finite dimension makes that map bijective.

The imported diagonal-corner reconstruction theorem then turns transfer similarity into the pointwise conjugacy equation. Repository and pinned-Mathlib searches found the transport, finite-rank, and corner dependencies used by the proof, but no theorem packaging the full displayed equivalence.

## References

- Truth anchor: `D5/S3/Observer/Dynamics/DiagonalInterfaceConjugacy.diagonal_interface_conjugacy`
- Dependency: [D5/S3/ObserverMemory/InverseLimits/DiagonalCornerReconstruction](../../ObserverMemory/InverseLimits/DiagonalCornerReconstruction.md)
