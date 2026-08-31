# Postprocessing Resolution Monotonicity

## Abstract

Deterministic postprocessing cannot refine an identification kernel.

**Theorem 1.1 (Postprocessing cannot improve identification resolution).**

$$\forall q: X \to Y, p: Y \to Z, \operatorname{ker}\left(q\right) \subseteq \operatorname{ker}\left(p \circ q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Postprocessing/PostprocessingResolutionMonotonicity.postprocessing_cannot_improve_identification_resolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a query profile and p any deterministic postprocessing map.

States with equal q-profiles remain equal after p is applied, so every original profile fiber remains inside one processed fiber.

The processed kernel may be equal or larger; ordinary function postprocessing cannot create a distinction absent from q.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Postprocessing/PostprocessingResolutionMonotonicity.postprocessing_cannot_improve_identification_resolution`
- Dependency: [D5/S3/ConceptDynamics/Postprocessing/PostprocessingKernelMonotonicity](PostprocessingKernelMonotonicity.md)
