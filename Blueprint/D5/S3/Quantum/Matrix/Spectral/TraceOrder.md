# Positivity and monotonicity of matrix traces

## Abstract

Positivity and monotonicity of matrix traces

FiniteType denotes a finite coordinate type with decidable equality. ReTr means the real part of the ordinary unnormalized matrix trace. The positive-product trace argument is the RHLinalg spectral proof from the attributed Zeta23 source; the weighted-order consequence is the positive-trace argument for inverse trace convexity.

**Theorem 1.1 (Positive products have nonnegative real trace).**

$$\forall k \in RCLike, n \in FiniteType, A \in \operatorname{Matrix}\left(n, n, k\right), B \in \operatorname{Matrix}\left(n, n, k\right),\; ((\operatorname{PosSemidef}\left(A\right)) \land (\operatorname{PosSemidef}\left(B\right))) \Rightarrow (0 \le \operatorname{ReTr}\left(A \cdot B\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Spectral/TraceOrder.trace_mul_nonneg_of_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive semidefinite A and B over any RCLike scalar type, ReTr(A B)>=0. Diagonalize A and cycle the trace. Each summand is a nonnegative eigenvalue of A times a nonnegative diagonal entry of a unitary conjugate of B. Neither A B nor B A is required to be Hermitian.

**Theorem 1.2 (A positive weight preserves trace order).**

$$\forall n \in FiniteType, A \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right), B \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right), C \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; ((\operatorname{PosSemidef}\left(C\right)) \land (A \le B)) \Rightarrow (\operatorname{ReTr}\left(C \cdot A\right) \le \operatorname{ReTr}\left(C \cdot B\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Spectral/TraceOrder.weighted_trace_re_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive semidefinite complex C and A <= B, ReTr(C A)<=ReTr(C B). The difference is ReTr(C(B-A)), which is nonnegative by positive-product trace positivity. No separate Hermitian hypothesis on A or B is required.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/Spectral/TraceOrder.trace_mul_nonneg_of_posSemidef`
- Truth anchor: `D5/S3/Quantum/Matrix/Spectral/TraceOrder.weighted_trace_re_mono`
