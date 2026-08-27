# Unified Sequential Kernel

## Abstract

All allowed sequential statistics determine one orthogonal residual.

**Theorem 1.1 (Allowed word equivalence is residual membership).**

$$\begin{gathered}\forall d: Nat, A, S: \operatorname{Type},\\{}W: \operatorname{Set}(\operatorname{List}(A)), J: A\to\operatorname{HermitianSpace}(d)\to\operatorname{HermitianSpace}(d),\\{}X: S\to\operatorname{HermitianSpace}(d), rho, sigma: S \Rightarrow\\{}(\forall w: \operatorname{List}(A), w \in W \Rightarrow \operatorname{inner}(\mathbb{R}, X(rho), \operatorname{sequentialWordEffect}(J, w)) = \operatorname{inner}(\mathbb{R}, X(sigma), \operatorname{sequentialWordEffect}(J, w))) \Leftrightarrow (X(rho) - X(sigma) \in (\operatorname{span}(\mathbb{R}, \{\operatorname{sequentialWordEffect}(J, w) \mid w \in W\}))^{\perp}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PredictionDepth/UnifiedSequentialKernel.unified_sequential_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observer supplies an allowed set of finite branch words. Each word uses the canonical source-order Heisenberg fold on the identity effect.

Two represented states agree on every allowed word exactly when their difference lies in the orthogonal complement of the real span of all allowed word effects.

## References

- Truth anchor: `D5/S3/Quantum/PredictionDepth/UnifiedSequentialKernel.unified_sequential_kernel`
- Dependency: [D5/S3/Quantum/Completion/SequentialWordObservationResidual](../Completion/SequentialWordObservationResidual.md)
