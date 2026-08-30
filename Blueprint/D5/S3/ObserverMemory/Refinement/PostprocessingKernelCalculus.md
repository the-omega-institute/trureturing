# Postprocessing Kernel Calculus

## Abstract

Postprocessing enlarges readout kernels, with equality exactly on injective realized postprocessing and strictness witnessed by a realized collision.

**Theorem 1.1 (Postprocessing Kernel le).**

$$\forall X: Type, Y: Type, Z: Type, q: X \to Y, postprocess: Y \to Z,\\{}(Setoid.ker q \leq Setoid.ker (postprocess \circ q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/PostprocessingKernelCalculus.postprocessing_kernel_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deterministic postprocessing can only enlarge the equality kernel.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Postprocessing Kernel eq iff Inj On Range).**

$$\forall X: Type, Y: Type, Z: Type, q: X \to Y, postprocess: Y \to Z,\\{}(Setoid.ker (postprocess \circ q) = Setoid.ker q \Leftrightarrow Set.InjOn postprocess (Set.range q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/PostprocessingKernelCalculus.postprocessing_kernel_eq_iff_injOn_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Postprocessing preserves exactly the original kernel iff it is injective on values that the original readout actually realizes.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Postprocessing Strict iff Range Collision).**

$$\forall X: Type, Y: Type, Z: Type, q: X \to Y, postprocess: Y \to Z,\\{}(Setoid.ker q < Setoid.ker (postprocess \circ q) \Leftrightarrow \exists x y, q x \neq q y \land postprocess (q x) = postprocess (q y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/PostprocessingKernelCalculus.postprocessing_strict_iff_range_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel growth is strict exactly when two realized readout values are separated before postprocessing and collide afterwards.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/PostprocessingKernelCalculus.postprocessing_kernel_eq_iff_injOn_range`
- Truth anchor: `D5/S3/ObserverMemory/Refinement/PostprocessingKernelCalculus.postprocessing_kernel_le`
- Truth anchor: `D5/S3/ObserverMemory/Refinement/PostprocessingKernelCalculus.postprocessing_strict_iff_range_collision`
