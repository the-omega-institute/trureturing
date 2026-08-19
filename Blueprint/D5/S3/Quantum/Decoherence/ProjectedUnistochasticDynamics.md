# Projected Unitary Dynamics

## Abstract

Projected unitary dynamics induces a doubly stochastic transition law.

**Theorem 1.1 (Projected unitary dynamics is a Markov chain).**

$$\forall I: \operatorname{FiniteType},\ \forall U\in \operatorname{UnitaryMatrices}(I),\ \forall p: I\to\mathbb{R},\ \forall n,\ \operatorname{projectedOrbit}(U, p, n) = \sum_{j} \operatorname{projectedWeights}(U, p, n)_{j} \operatorname{basisProjector}(j) \land \forall k, j,\ \operatorname{transitionMatrix}(U)_{kj} = \Vert U_{kj} \Vert^{2} \land \operatorname{transitionMatrix}(U) \in \operatorname{DoublyStochastic}(I) \land \forall n,\ \operatorname{projectedWeights}(U, p, n+1) = \operatorname{transitionMatrix}(U) \operatorname{projectedWeights}(U, p, n).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.projected_dynamics_is_unistochastic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U be a finite unitary matrix written in measurement-basis coordinates. Starting from arbitrary real diagonal weights, form the state orbit by repeatedly conjugating with U and projecting onto the measurement-basis diagonal. The displayed weights are read back from that orbit; they are not defined by the recurrence.

Every state in the post-projection orbit is the sum of its weights times the coordinate rank-one projectors. The transition entry from j to k is the squared norm of U at (k,j), and the full weight vector is advanced by multiplication with this matrix.

The existing repository theorem normSqMatrix_mem_doublyStochastic_of_unitary is applied directly to prove that the transition matrix is doubly stochastic. Local matrix-entry calculations establish the diagonal decomposition and recurrence.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics.projected_dynamics_is_unistochastic`
