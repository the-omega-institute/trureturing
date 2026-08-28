# Lossless Linear Postprocessing

## Abstract

A linear postprocessing preserves the observation kernel exactly when it is injective on the observed range.

**Theorem 1.1 (Kernel preservation is range injectivity).**

$$\begin{gathered}\forall K, V, Y, Z: Type, M, B,\\{}\operatorname{Ring}(K) \land \operatorname{AddCommGroup}(V) \land \operatorname{Module}(K, V) \land \operatorname{AddCommGroup}(Y) \land \operatorname{Module}(K, Y),\\{}\operatorname{AddCommGroup}(Z) \land \operatorname{Module}(K, Z) \land M \in \operatorname{LinearMap}(K, V, Y) \land B \in \operatorname{LinearMap}(K, Y, Z) \Rightarrow\\{}\operatorname{ker}(\operatorname{comp}(B, M)) = \operatorname{ker}(M) \iff \operatorname{InjOn}(B, \operatorname{range}(M)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/LosslessLinearPostprocessing.kernel_comp_eq_iff_injective_on_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward direction tests two realized observations through their difference. The reverse direction compares each observed value with the observed zero, so injectivity on the realized range recovers the original kernel.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/LosslessLinearPostprocessing.kernel_comp_eq_iff_injective_on_range`
