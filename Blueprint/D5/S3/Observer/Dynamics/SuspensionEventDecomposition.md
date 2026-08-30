# Suspension Event Decomposition

## Abstract

A positive-roof suspension flow splits uniquely into event count and residual phase.

**Theorem 1.1 (Continuous time has a unique event-phase decomposition).**

$$\begin{gathered}\forall K: \operatorname{Type},\\{}[\operatorname{TopologicalSpace}\left(K\right)], [\operatorname{CompactSpace}\left(K\right)],\\{}T: \operatorname{Homeomorph}\left(K, K\right), r: K \to \mathbb{R},\\{}\operatorname{Continuous}\left(r\right) \land (\forall x: K, 0 < \operatorname{r}\left(x\right)),\\{}k: K, u: RoofCoordinate, t: \mathbb{R}, 0 \leq t\\{}\Rightarrow \exists! normal: \mathbb{N} \times RoofCoordinate,\\{}\operatorname{birkhoffSum}\left(T, r, \operatorname{fst}\left(normal\right), k\right) \leq \operatorname{physicalHeight}\left(r, k, u\right) + t \land\\{}\operatorname{physicalHeight}\left(r, k, u\right) + t < \operatorname{birkhoffSum}\left(T, r, \operatorname{fst}\left(normal\right) + 1, k\right) \land\\{}\operatorname{physicalHeight}\left(r, \operatorname{iterate}\left(T, \operatorname{fst}\left(normal\right), k\right), \operatorname{snd}\left(normal\right)\right) = \operatorname{physicalHeight}\left(r, k, u\right) + t - \operatorname{birkhoffSum}\left(T, r, \operatorname{fst}\left(normal\right), k\right) \land\\{}\operatorname{suspensionFlow}\left(T, r, t, \operatorname{canonicalSuspensionClass}\left(T, r, k, u\right)\right) = \operatorname{canonicalSuspensionClass}\left(T, r, \operatorname{iterate}\left(T, \operatorname{fst}\left(normal\right), k\right), \operatorname{snd}\left(normal\right)\right) \land\\{}\operatorname{physicalHeight}\left(r, k, u\right) + t = \operatorname{birkhoffSum}\left(T, r, \operatorname{fst}\left(normal\right), k\right) + \operatorname{physicalHeight}\left(r, \operatorname{iterate}\left(T, \operatorname{fst}\left(normal\right), k\right), \operatorname{snd}\left(normal\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Dynamics/SuspensionEventDecomposition.continuous_time_discrete_event_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen suspension carrier uses a normalized leaf coordinate. Multiplication by the positive roof gives its nonnegative physical phase, so no separate sign hypothesis is needed.

Literal forward translation is first performed on a private nonnegative-height cover. Normalization respects every roof crossing and transports the translated class back to the canonical suspension quotient.

Compactness and roof positivity force the Birkhoff sums past the translated physical phase. The least crossing index supplies both half-open bounds; division by the final positive roof produces the residual leaf coordinate.

The bounds determine the event count uniquely, while positivity makes physical height injective within the final leaf. Thus the discrete count and residual coordinate are jointly unique and recover the complete translated time coordinate.

## References

- Truth anchor: `D5/S3/Observer/Dynamics/SuspensionEventDecomposition.continuous_time_discrete_event_decomposition`
- Dependency: [D5/S3/Observer/Dynamics/MinimalSuspensionContinuum](MinimalSuspensionContinuum.md)
