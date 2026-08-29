# Recoverable Postprocessing Kernel Equality

## Abstract

Recoverable postprocessing preserves the readout kernel exactly.

**Theorem 1.1 (Recovery on the readout image preserves the kernel).**

$$\forall q: X \to Y, p: Y \to Z, r: Z \to Y,\\{}(\forall x: X, \operatorname{r}\left(\operatorname{p}\left(\operatorname{q}\left(x\right)\right)\right) = \operatorname{q}\left(x\right)) \Rightarrow \operatorname{ker}\left(p \circ q\right) = \operatorname{ker}\left(q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Postprocessing/RecoverablePostprocessingKernelEquality.recoverable_postprocessing_preserves_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a readout, p a postprocessing map, and r a recovery map from processed values to original readout values.

Assume r(p(q(x))) = q(x) for every source state x. Recovery then reflects processed equality, while p preserves original equality.

The two equality kernels coincide. Recovery is required only on values in the image of q, not on every value of the output type.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Postprocessing/RecoverablePostprocessingKernelEquality.recoverable_postprocessing_preserves_kernel`
