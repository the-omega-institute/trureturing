# Injective Postprocessing Kernel Equality

## Abstract

Injective postprocessing preserves an observation kernel exactly.

**Theorem 1.1 (Injective postprocessing preserves pointwise kernel membership).**

$$\forall q: X \to Y, p: Y \to Z, x, y: X, \operatorname{Injective}\left(p\right) \Rightarrow (\operatorname{Kernel}\left(p \circ q, x, y\right) \iff \operatorname{Kernel}\left(q, x, y\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Postprocessing/InjectivePostprocessingKernelEquality.injective_postprocessing_preserves_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a readout and p an injective postprocessing map. Fix two source states x and y.

Equality before processing is preserved by p, while equality after processing is reflected by injectivity of p.

The theorem is pointwise in x and y and therefore states exactly the equivalence of their original and processed kernel memberships.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Postprocessing/InjectivePostprocessingKernelEquality.injective_postprocessing_preserves_kernel`
