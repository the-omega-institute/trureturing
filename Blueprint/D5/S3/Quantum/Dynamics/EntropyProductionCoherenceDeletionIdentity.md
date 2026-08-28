# Entropy Production by Coherence Deletion

## Abstract

Unitary evolution followed by coordinate-basis pinching produces entropy equal to the deleted coherence, with nonnegative gains that telescope.

**Theorem 1.1 (Entropy production equals deleted coherence).**

$$\begin{gathered}\forall n: \operatorname{Type}, U: \operatorname{Matrix}\left(n, n, \mathbb{C}\right), \rho: \mathbb{N} \mapsto \operatorname{DensityState}\left(n\right),\\{}\operatorname{Fintype}\left(n\right) \land \operatorname{DecidableEq}\left(n\right) \land U \in \operatorname{unitaryGroup}\left(n, \mathbb{C}\right) \land\\{}\forall k \in \mathbb{N}, \rho_{k+1} = \operatorname{basisPinchingState}\left(\operatorname{unitaryConjugateState}\left(U, \rho_{k}\right)\right) \Rightarrow\\{}(\forall k \in \mathbb{N}, (\operatorname{vonNeumannEntropy}\left(\rho_{k+1}\right) - \operatorname{vonNeumannEntropy}\left(\rho_{k}\right) = \operatorname{quantumRelativeEntropy}\left(\operatorname{unitaryConjugateState}\left(U, \rho_{k}\right), \operatorname{basisPinchingState}\left(\operatorname{unitaryConjugateState}\left(U, \rho_{k}\right)\right)\right) \land 0 \leq \operatorname{quantumRelativeEntropy}\left(\operatorname{unitaryConjugateState}\left(U, \rho_{k}\right), \operatorname{basisPinchingState}\left(\operatorname{unitaryConjugateState}\left(U, \rho_{k}\right)\right)\right))) \land\\{}(\forall N \in \mathbb{N}, \operatorname{vonNeumannEntropy}\left(\rho_{N}\right) - \operatorname{vonNeumannEntropy}\left(\rho_{0}\right) = \sum_{k < N} \operatorname{quantumRelativeEntropy}\left(\operatorname{unitaryConjugateState}\left(U, \rho_{k}\right), \operatorname{basisPinchingState}\left(\operatorname{unitaryConjugateState}\left(U, \rho_{k}\right)\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.entropy_production_coherence_deletion_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U be a unitary complex matrix on a finite decidable carrier. Starting from a sequence of density states, assume each next state is obtained by conjugating with U and then deleting the off-diagonal entries in the fixed coordinate basis.

At every step, the entropy gain is exactly the quantum relative entropy from the evolved state to its pinched state, and this quantity is nonnegative. Summing these one-step identities gives the finite-horizon entropy balance.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.entropy_production_coherence_deletion_identity`
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](../../Divergence/GrandmotherTheorem.md)
- Dependency: [D5/S3/Quantum/Divergence/VonNeumannEntropyPinching](../Divergence/VonNeumannEntropyPinching.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
