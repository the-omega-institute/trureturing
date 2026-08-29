# Bidirectional Transformation Description Bound

## Abstract

Two inverse compilers bound both description costs and their distance.

**Theorem 1.1 (Two described transformations bound both endpoint complexities).**

$$\begin{gathered}\forall Object, Transformation, ObjectCode, TransformationCode: \operatorname{Type},\\{}\forall objects: \operatorname{DescriptionSystem}\left(Object, ObjectCode\right),\\{}\forall transformations: \operatorname{DescriptionSystem}\left(Transformation, TransformationCode\right),\\{}\forall applies: Transformation \to Object \to Object \to \operatorname{Prop},\\{}\forall forwardOverhead, reverseOverhead: \mathbb{N},\\{}\forall forwardCompiler: \operatorname{TransformationCompiler}\left(objects, transformations, objects, applies, forwardOverhead\right),\\{}\forall reverseCompiler: \operatorname{TransformationCompiler}\left(objects, transformations, objects, applies, reverseOverhead\right),\\{}\forall u, v: Transformation,\\{}\forall x, y: Object,\\{}(applies(u,x,y) \land applies(v,y,x)) \Rightarrow \\{}(K_{objects}(y) \leq K_{objects}(x) + K_{transformations}(u) + forwardOverhead) \land \\{}(K_{objects}(x) \leq K_{objects}(y) + K_{transformations}(v) + reverseOverhead) \land \\{}\operatorname{dist}\left(K_{objects}(x), K_{objects}(y)\right) \leq \operatorname{max}\left(K_{transformations}(u), K_{transformations}(v)\right) + \operatorname{max}\left(forwardOverhead, reverseOverhead\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DescriptionComplexity/BidirectionalTransformationDescriptionBound.bidirectional_transformation_description_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Objects and transformations use the canonical description-system family. One application relation records both directions, and each compiler combines an endpoint description with a transformation description.

The two application premises state that the forward transformation sends x to y and the reverse transformation sends y to x. Applying the frozen one-way compiler theorem in each direction gives the first two public inequalities.

A case split on the ordering of the two endpoint complexities turns their natural-number distance into one subtraction. The corresponding directional bound is then enlarged by the maxima of the transformation costs and fixed compiler overheads.

Pinned Mathlib was searched for natural-distance lemmas and supplies Nat.dist_eq_sub_of_le and Nat.dist_eq_sub_of_le_right. The repository-wide description-complexity search found only the imported one-way predecessor; no theorem containing all three public clauses was present.

## References

- Truth anchor: `D5/S0/Computability/DescriptionComplexity/BidirectionalTransformationDescriptionBound.bidirectional_transformation_description_bounds`
- Dependency: [D5/S0/Computability/DescriptionComplexity/TransformationDescriptionBound](TransformationDescriptionBound.md)
