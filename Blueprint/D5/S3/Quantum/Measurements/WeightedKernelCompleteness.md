# Weighted Kernel Completeness

## Abstract

Strictly positive weighted effect quadratics have the common trace-effect kernel and are positive exactly under informational completeness.

**Theorem 1.1 (Positive weights preserve the common effect kernel).**

$$\forall d: \operatorname{Nat}, \operatorname{NeZero}(d), I: \operatorname{Type}, [\operatorname{Fintype}(I)], e: I \to \operatorname{traceZeroHermitian}(d), w: I \to \mathbb{R}, \forall i: I, 0 < \operatorname{w}(i) \Rightarrow \{D \mid \operatorname{weightedGramian}(e, w, D) = 0\} = \{D \mid \forall i: I, \operatorname{Tr}(D e_{i}) = 0\} \land \forall D: \operatorname{traceZeroHermitian}(d), D \neq 0 \Rightarrow 0 < \operatorname{weightedGramian}(e, w, D) \iff \operatorname{Injective}(D: \operatorname{traceZeroHermitian}(d) \mapsto (i: I \mapsto \operatorname{Tr}(D e_{i}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/WeightedKernelCompleteness.weighted_kernel_completeness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the real traceless-Hermitian carrier, the weighted Gramian is the finite sum of the positive effect weights times squared trace-effect coordinates.

Strict positivity forces its kernel to be exactly the intersection of the individual effect kernels. The quadratic form is positive definite precisely when the effect-coordinate readout is injective.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/WeightedKernelCompleteness.weighted_kernel_completeness`
- Dependency: [D5/S3/Quantum/Measurement/OperationalObservationKernel](../Measurement/OperationalObservationKernel.md)
