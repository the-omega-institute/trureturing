# Birth Stage Filtration

## Abstract

Every eventually present object in an append-only filtration has a unique first stage.

**Theorem 1.1 (Birth is the unique first stage).**

$$\begin{gathered}\forall stage: Nat \to \operatorname{Set}\left(V\right), node: V, level: Nat,\\{}(\exists n: Nat, node \in \operatorname{stage}\left(n\right)) \land node \in \operatorname{stage}\left(level\right) \land\\{}(\forall earlier: Nat, earlier < level \Rightarrow \neg (node \in \operatorname{stage}\left(earlier\right))) \Rightarrow\\{}\operatorname{birthStage}\left(stage, node\right) = level.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/BirthStageFiltration.birthStage_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a stage family and a node that occurs at some stage. If a chosen level contains the node and every earlier level omits it, that level is the birth stage.

The existence, presence, and absence assumptions all appear in the antecedent. Append-only monotonicity is not needed for this uniqueness statement and is not asserted.

**Theorem 1.2 (Append-only stages retain every born node).**

$$\forall stage: Nat \to \operatorname{Set}\left(V\right), node: V, level: Nat,\\{}(\operatorname{AppendOnly}\left(stage\right) \land (\exists n: Nat, node \in \operatorname{stage}\left(n\right)) \land\\{}\operatorname{birthStage}\left(stage, node\right) \leq level) \Rightarrow\\{}node \in \operatorname{stage}\left(level\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/BirthStageFiltration.mem_of_birthStage_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the stage family is append-only and the node eventually appears. Every level at or after its birth contains it.

The conclusion is conditional on both eventual presence and the displayed birth-stage inequality; it does not assert earlier membership.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/BirthStageFiltration.birthStage_unique`
- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/BirthStageFiltration.mem_of_birthStage_le`
