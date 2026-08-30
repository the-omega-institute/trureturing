# Transversal Fixed Point

## Abstract

A coherent family of states across semiconjugate world models forms a transversal fixed point whenever one anchor state is fixed.

**Theorem 1.1 (Transport From Fixed Is Fixed).**

$$\forall Index: Type, model: WorldModelDiagram Index, anchor: Index, state: model.State anchor,\\{}(Function.IsFixedPt (model.step anchor) state) \Rightarrow\\{}(model.IsFixedSection (model.transportFrom anchor state)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/TransversalFixedPoint.transport_from_fixed_is_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fixed anchor transports to a fixed state in every target world model.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Coherent Section Fixed From Anchor).**

$$\forall Index: Type, model: WorldModelDiagram Index, state: model.Section, anchor: Index,\\{}(model.IsCoherentSection state) \land (Function.IsFixedPt (model.step anchor) (state anchor)) \Rightarrow\\{}(model.IsFixedSection state).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/TransversalFixedPoint.coherent_section_fixed_from_anchor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A coherent section that is fixed at one anchor is fixed in every model.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Fixed At Anchor iff Fixed At Target Of Injective).**

$$\forall Index: Type, model: WorldModelDiagram Index, state: model.Section, anchor: Index, target: Index,\\{}(model.IsCoherentSection state) \land (Function.Injective (model.bridge anchor target)) \Rightarrow\\{}(Function.IsFixedPt (model.step anchor) (state anchor) \Leftrightarrow Function.IsFixedPt (model.step target) (state target)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/TransversalFixedPoint.fixed_at_anchor_iff_fixed_at_target_of_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a coherent section, fixedness at any two anchors is equivalent when the bridge in one direction is injective.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Observer/WorldModel/TransversalFixedPoint.coherent_section_fixed_from_anchor`
- Truth anchor: `D5/S3/Observer/WorldModel/TransversalFixedPoint.fixed_at_anchor_iff_fixed_at_target_of_injective`
- Truth anchor: `D5/S3/Observer/WorldModel/TransversalFixedPoint.transport_from_fixed_is_fixed`
- Dependency: [D5/S3/Observer/Bridges/FixedPointSemiconjugacy](../Bridges/FixedPointSemiconjugacy.md)
