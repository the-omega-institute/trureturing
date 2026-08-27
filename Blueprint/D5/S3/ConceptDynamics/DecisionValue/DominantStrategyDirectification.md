# Dominant-Strategy Directification

## Abstract

Dominant strategies induce truthful dominance in the direct mechanism.

**Theorem 1.1 (Truthful reports remain dominant after directification).**

$$\forall n \in \mathbb{N}, T, M: \operatorname{Fin}\left(n\right) \to Type, O: Type,\\{}G: \prod_{i \in \operatorname{Fin}\left(n\right)} M(i) \to O, \forall i \in \operatorname{Fin}\left(n\right), S_{i}: T(i) \to M(i),\\{}\forall i \in \operatorname{Fin}\left(n\right), U_{i}: T(i) \to O \to \mathbb{R},\\{}{\forall i \in \operatorname{Fin}\left(n\right), t \in T(i), m \in \prod_{i \in \operatorname{Fin}\left(n\right)} M(i), a \in M(i), U(i, t, G(\operatorname{update}\left(m, i, S(i, t)\right))) \geq U(i, t, G(\operatorname{update}\left(m, i, a\right)))} \Rightarrow\\{}D: \prod_{i \in \operatorname{Fin}\left(n\right)} T(i) \to O, D(r: \prod_{i \in \operatorname{Fin}\left(n\right)} T(i)) := G(\lambda j: \operatorname{Fin}\left(n\right) \mapsto S(j, r(j))),\\{}{\forall i \in \operatorname{Fin}\left(n\right), t \in T(i), r \in \prod_{i \in \operatorname{Fin}\left(n\right)} T(i), q \in T(i), U(i, t, D(\operatorname{update}\left(r, i, t\right))) \geq U(i, t, D(\operatorname{update}\left(r, i, q\right)))}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/DominantStrategyDirectification.dominant_strategy_directification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Agents are indexed by Fin n and may have different type and message spaces. The original mechanism consumes a dependent message profile, and each utility evaluates outcomes at one agent's true type.

The public hypothesis says each strategy weakly dominates every alternative own message for every profile of the other messages. The direct mechanism is publicly constructed by applying all strategies to the reported type profile before invoking the original mechanism.

Updating one reported type and then applying the strategy family equals updating the induced message profile at that agent. The original dominance inequality therefore applies directly, proving truthful reporting weakly dominates every alternative report.

Repository and pinned-library searches found no exact directification theorem. The proof directly applies the pinned coordinate-update lemmas for the dependent profiles.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/DominantStrategyDirectification.dominant_strategy_directification`
