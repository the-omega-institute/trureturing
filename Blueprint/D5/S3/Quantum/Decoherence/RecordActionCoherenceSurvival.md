# Record Action Controls Coherence Survival

## Abstract

Normalized record overlaps control coherence survival and its logarithmic rate.

**Theorem 1.1 (Record action controls coherence survival).**

$$\forall I \in Type, E \in Type, R \in \mathbb{N} \to \left(I \to E\right), i \in I, j \in I, rho0 \in \mathbb{C},\; \left(\left(\operatorname{NormedAddCommGroup}\left(E\right) \land \operatorname{InnerProductSpace}\left(\mathbb{C}, E\right)\right) \land \left(\left(\forall r \in \mathbb{N}, i \in I,\; \left\lVert R\left(r, i\right) \right\rVert = 1\right) \land rho0 \ne 0\right)\right) \Rightarrow \operatorname{let} g: \mathbb{N} \to \mathbb{C} = r: \mathbb{N} \mapsto \operatorname{inner}\left(R\left(r, j\right), R\left(r, i\right)\right);\operatorname{let} Gamma: \mathbb{N} \to \mathbb{C} = N: \mathbb{N} \mapsto \operatorname{rangeProduct}\left(N, g\right);\operatorname{let} A: \mathbb{N} \to [0, \infty] = N: \mathbb{N} \mapsto \operatorname{toENNReal}\left(\operatorname{negLog}\left(\operatorname{ofReal}\left(\left\lVert Gamma\left(N\right) \right\rVert\right)\right)\right);\operatorname{let} rho: \mathbb{N} \to \mathbb{C} = N: \mathbb{N} \mapsto Gamma\left(N\right) \cdot rho0;\left(\forall N \in \mathbb{N},\; \operatorname{ofReal}\left(\left\lVert rho\left(N\right) \right\rVert\right) = \operatorname{exp}\left(-\operatorname{coeEReal}\left(A\left(N\right)\right)\right) \cdot \operatorname{ofReal}\left(\left\lVert rho0 \right\rVert\right)\right) \land \left(\operatorname{Monotone}\left(A\right) \land \left(\forall lambda \in EReal,\; \operatorname{TendstoAtTop}\left(N, \mathbb{N}, \frac{\operatorname{coeEReal}\left(A\left(N\right)\right)}{\operatorname{coeEReal}\left(N\right)}, lambda\right) \Rightarrow \operatorname{TendstoAtTop}\left(N, \mathbb{N}, \frac{\operatorname{negLog}\left(\frac{\operatorname{ofReal}\left(\left\lVert rho\left(N\right) \right\rVert\right)}{\operatorname{ofReal}\left(\left\lVert rho0 \right\rVert\right)}\right)}{\operatorname{coeEReal}\left(N\right)}, lambda\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/RecordActionCoherenceSurvival.record_action_controls_coherence_survival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each record overlap is constructed from the Hilbert inner product of the normalized record vectors. Their finite product defines the surviving coherence, and its extended negative logarithm defines the record action.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/RecordActionCoherenceSurvival.record_action_controls_coherence_survival`
- Dependency: [D5/S3/Quantum/PureState/RecordCoherenceComplementarity](../PureState/RecordCoherenceComplementarity.md)
