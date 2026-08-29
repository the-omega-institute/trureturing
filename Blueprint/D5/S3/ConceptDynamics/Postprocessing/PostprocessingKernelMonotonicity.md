# Postprocessing Kernel Monotonicity

## Abstract

Postprocessing can only enlarge a readout equality kernel.

**Theorem 1.1 (Postprocessing only enlarges the equality kernel).**

$$\forall q: X \to Y, p: Y \to Z, \operatorname{ker}\left(q\right) \subseteq \operatorname{ker}\left(p \circ q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Postprocessing/PostprocessingKernelMonotonicity.postprocessing_kernel_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an arbitrary readout q and deterministic postprocessing map p.

Any equality q(x) = q(y) remains an equality after applying p, so every original collision lies in the processed kernel.

Only non-strict inclusion is claimed; p may preserve the kernel exactly or identify additional source pairs.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Postprocessing/PostprocessingKernelMonotonicity.postprocessing_kernel_mono`
