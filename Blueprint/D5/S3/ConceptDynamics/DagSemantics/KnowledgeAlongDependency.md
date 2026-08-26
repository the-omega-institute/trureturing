# Knowledge Along Dependency

## Abstract

Readout refinement along dependency paths enlarges answerability and shrinks target defects.

**Theorem 1.1 (Answerable questions grow along dependency paths).**

$$\begin{gathered}\forall Coordinate: Node \to Type, edge: Node \to Node \to Prop,\\{}readout: (\forall node: Node, \operatorname{Concept}\left(State, \operatorname{Coordinate}\left(node\right)\right)), first, last: Node,\\{}(\operatorname{EdgeRefines}\left(edge, readout\right) \land \operatorname{ReflTransGen}\left(edge, first, last\right)) \Rightarrow\\{}\operatorname{AnswerableQuestions}\left(\operatorname{readout}\left(first\right)\right) \subseteq \operatorname{AnswerableQuestions}\left(\operatorname{readout}\left(last\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/KnowledgeAlongDependency.answerableQuestions_mono_of_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume each dependency edge carries the displayed readout refinement. Along a supplied reflexive-transitive path, questions answerable at the first readout remain answerable at the last.

The result is a set inclusion for the two endpoint readouts. It does not assert equality of answerable-question families.

**Theorem 1.2 (Target risk shrinks along dependency paths).**

$$\begin{gathered}\forall Coordinate: Node \to Type, edge: Node \to Node \to Prop,\\{}readout: (\forall node: Node, \operatorname{Concept}\left(State, \operatorname{Coordinate}\left(node\right)\right)), first, last: Node, targets: \operatorname{Set}\left(\operatorname{Concept}\left(State, Target\right)\right),\\{}(\operatorname{EdgeRefines}\left(edge, readout\right) \land \operatorname{ReflTransGen}\left(edge, first, last\right)) \Rightarrow\\{}\operatorname{targetRisk}\left(\operatorname{readout}\left(last\right), targets\right) \subseteq \operatorname{targetRisk}\left(\operatorname{readout}\left(first\right), targets\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/KnowledgeAlongDependency.targetRisk_antitone_of_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same refinement-carrying path and a displayed set of target readouts, every risk pair remaining at the last node was already a risk pair at the first.

The target set is fixed on both sides of the inclusion; the theorem makes no comparison between different target families.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/KnowledgeAlongDependency.answerableQuestions_mono_of_reachable`
- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/KnowledgeAlongDependency.targetRisk_antitone_of_reachable`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/QuestionAlgebraDuality](../DefinitionEscape/QuestionAlgebraDuality.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementTransitivity](../Refinement/RefinementTransitivity.md)
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
