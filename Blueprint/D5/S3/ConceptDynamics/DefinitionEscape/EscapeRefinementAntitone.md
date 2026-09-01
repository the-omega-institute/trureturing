# Escape Refinement Antitonicity

## Abstract

Refining an observer family can only shrink its target defect and primitive escape.

**Theorem 1.1 (Selected observer refinement shrinks target escape).**

$$\begin{aligned}\forall I: Type, X: Type, C: Type, Target: Type,\\V: I \to Type,\\S: \operatorname{Set}\left(I\right), S': \operatorname{Set}\left(I\right),\\definitions: \forall i: I, \operatorname{Concept}\left(X, V(i)\right),\\q: \operatorname{Concept}\left(X, C\right), target: \operatorname{Concept}\left(X, Target\right),\\S \subseteq S' \Rightarrow \operatorname{defectRelation}\left(\operatorname{conceptJoin}\left(q, \operatorname{jointReadout}\left(\operatorname{restrict}\left(definitions, S'\right)\right)\right), target\right) \subseteq \operatorname{defectRelation}\left(\operatorname{conceptJoin}\left(q, \operatorname{jointReadout}\left(\operatorname{restrict}\left(definitions, S\right)\right)\right), target\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/EscapeRefinementAntitone.escape_refinement_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary index, state, baseline, and target types, V is a dependent observer-codomain family and definitions supplies one concept at each index. The only order datum is S contained in S'.

Equality of the refined joint readout restricts pointwise to every index in S, while the target inequality is unchanged. Hence the defect relation for S' is contained in the defect relation for S without finiteness, inhabitedness, or target-side premises.

**Theorem 1.2 (Intersection-kernel primitive escape is antitone).**

$$\begin{aligned}\forall X: Type, InputOutput: Type, Output: Type,\\Gamma: \operatorname{Set}\left(\operatorname{Concept}\left(X, InputOutput\right)\right), Delta: \operatorname{Set}\left(\operatorname{Concept}\left(X, InputOutput\right)\right),\\Gamma \subseteq Delta \Rightarrow \{candidate: \operatorname{Concept}\left(X, Output\right) | \operatorname{PrimitiveEscape}\left(Delta, candidate\right)\} \subseteq \{candidate: \operatorname{Concept}\left(X, Output\right) | \operatorname{PrimitiveEscape}\left(Gamma, candidate\right)\}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/EscapeRefinementAntitone.primitive_escape_refinement_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Gamma and Delta are homogeneous concept families with Gamma contained in Delta. PrimitiveEscape is the accepted complement of semantic closure, whose relation carrier is the intersection jointKernel.

The accepted jointKernel_antitone law sends every Delta-kernel pair to a Gamma-kernel pair. A candidate outside the larger semantic closure is therefore outside the smaller closure. This is the intersection-family form of the finite-window law above.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/EscapeRefinementAntitone.escape_refinement_antitone`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/EscapeRefinementAntitone.primitive_escape_refinement_antitone`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois](DefinitionKernelGalois.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting](FiniteCoverCounting.md)
