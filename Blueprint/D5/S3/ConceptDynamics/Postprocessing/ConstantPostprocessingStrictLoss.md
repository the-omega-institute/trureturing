# Constant Postprocessing Strict Loss

## Abstract

Constant postprocessing strictly loses every witnessed distinction.

**Theorem 1.1 (Constant postprocessing strictly enlarges the kernel).**

$$\forall q: X \to Y, c: Z, x, y: X, \operatorname{q}\left(x\right) \neq \operatorname{q}\left(y\right) \Rightarrow \operatorname{ker}\left(q\right) < \operatorname{ker}\left(value \mapsto c \circ q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Postprocessing/ConstantPostprocessingStrictLoss.constant_postprocessing_strictly_enlarges_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a readout that separates a displayed pair x and y, and replace every readout value by one fixed processed value.

All original collisions remain collisions after postprocessing, while the witness pair becomes a new collision.

The conclusion is strict kernel inclusion from that witness. It does not assert that the original readout is globally injective.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Postprocessing/ConstantPostprocessingStrictLoss.constant_postprocessing_strictly_enlarges_kernel`
- Dependency: [D5/S3/ConceptDynamics/Postprocessing/PostprocessingKernelMonotonicity](PostprocessingKernelMonotonicity.md)
