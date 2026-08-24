# Measure Capture Submodularity

## Abstract

Arbitrary measures make residual-intersection capture submodular.

**Theorem 1.1 (Residual-intersection capture is submodular for every measure).**

$$\forall Edge, Definition: Type,\ [\operatorname{MeasurableSpace}\left(Edge\right)], nu: \operatorname{Measure}\left(Edge\right), residual: \operatorname{Set}\left(Edge\right), cut: Definition \to \operatorname{Set}\left(Edge\right), A, B: \operatorname{Set}\left(Definition\right),\ \operatorname{apply}\left(nu, \operatorname{apply}\left(captured, \operatorname{union}\left(A, B\right)\right)\right) + \operatorname{apply}\left(nu, \operatorname{apply}\left(captured, \operatorname{intersection}\left(A, B\right)\right)\right) \leq \operatorname{apply}\left(nu, \operatorname{apply}\left(captured, A\right)\right) + \operatorname{apply}\left(nu, \operatorname{apply}\left(captured, B\right)\right),\quad \text{where} \operatorname{apply}\left(captured, S\right) = \operatorname{intersection}\left(residual, \operatorname{iUnion}\left(definition \in S, \operatorname{apply}\left(cut, definition\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/MeasureCapture.measure_capture_submodular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula is equal in strength to measure_capture_submodular and to conjunct six of directly_provable_laws. Edge and Definition are the two Lean types; MeasurableSpace, Measure, and Set are the corresponding Mathlib type constructors; and nu, residual, cut, A, and B are the theorem's explicit arguments.

The displayed name captured is exactly the theorem-local function S => residual intersection iUnion definition in S, cut definition. Formula calls named apply are ordinary Lean function application; union, intersection, and iUnion are respectively Set union, Set intersection, and the bounded iterated union in that local definition. No displayed name introduces an extra predicate or hypothesis.

The reusable helper measure_union_add_inter_le_arbitrary proves the underlying arbitrary-set measure inequality by replacing the right set with a same-measure measurable hull. The public theorem identifies capture of A union B with the union of the two capture sets and includes capture of A intersection B in their intersection, yielding exactly the displayed inequality without a measurability premise on residual or cut.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/MeasureCapture.measure_capture_submodular`
