# Finite graph estimates and Kraus amplitudes

## Abstract

Finite connected relations propagate uniform edge estimates to all pairs. Pure-state channel survival is the sum of squared Kraus amplitudes.

**Theorem 1.1 (kraus_survival).**

$$\forall a \in Type,\; [\operatorname{Fintype}\left(a\right)] \forall r \in \mathbb{N}, psi \in a \to \mathbb{C}, K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(a, a, \mathbb{C}\right),\; \operatorname{Complex}.\operatorname{re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(psi\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\sum_{j : \operatorname{Fin}\left(r\right)} K\left(j\right) \cdot \operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(psi\right) \cdot \operatorname{Matrix}.\operatorname{conjTranspose}\left(K\left(j\right)\right), psi\right)\right)\right) = \sum_{j : \operatorname{Fin}\left(r\right)} \Vert \operatorname{dotProduct}\left(\operatorname{star}\left(psi\right), \operatorname{Matrix}.\operatorname{mulVec}\left(K\left(j\right), psi\right)\right) \Vert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingCore.kraus_survival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The channel action is expanded as the sum of Kj times the input projector times the conjugate transpose of Kj. Each term contributes the squared modulus of the corresponding survival amplitude. No normalization of the vector or trace-preservation assumption is needed.

**Theorem 1.2 (finite_graph_squared_distance_bound).**

$$\forall iota \in Type, E \in Type,\; [\operatorname{Fintype}\left(iota\right)] [\operatorname{NormedAddCommGroup}\left(E\right)] \forall r \in iota \to \left(iota \to Prop\right),\; \left(\forall i \in iota, j \in iota,\; \operatorname{Relation}.\operatorname{EqvGen}\left(r, i, j\right)\right) \Rightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall v \in iota \to E, eta \in \mathbb{R},\; 0 \le eta \Rightarrow \left(\left(\forall a \in iota, b \in iota,\; r\left(a, b\right) \Rightarrow \Vert v\left(a\right) - v\left(b\right) \Vert^{2} \le eta\right) \Rightarrow \left(\forall i \in iota, j \in iota,\; \Vert v\left(i\right) - v\left(j\right) \Vert^{2} \le C \cdot eta\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingCore.finite_graph_squared_distance_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite relation whose generated equivalence relation connects every pair, a positive constant controls every squared pair distance by any common nonnegative squared edge bound. The constant depends on the relation, and works for all maps into the normed additive group.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingCore.finite_graph_squared_distance_bound`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingCore.kraus_survival`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Measurement/ExactConditionalPreparationCost](../Measurement/ExactConditionalPreparationCost.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
