# TraceInverseConvexity

## Abstract

Trace convexity of inverse positive matrices.

**Theorem 1.1 (Weighted inverse trace on the positive cone).**

$$\forall d: \operatorname{Type}(), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ C: \operatorname{Matrix}(d, d, \mathbb{C}), \operatorname{PosSemidef}(C) \implies\ \operatorname{ConvexOn}(\mathbb{R}, \operatorname{PosDefCone}(\operatorname{Matrix}(d, d, \mathbb{C})), \Lambda A\mapsto\operatorname{ReTr}(C, \operatorname{inverse}(A)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/TraceInverseConvexity.weighted_trace_inverse_convexOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite complex matrix dimension and every positive semidefinite witness C, the real trace Re Tr(C A⁻¹) is convex in a positive-definite matrix A. The proof first applies Mathlib's operator convexity of Ring.inverse, then uses the positive-semidefinite trace product bound to descend the matrix order inequality to a scalar inequality. The unweighted inverse trace is the identity-witness specialization.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/TraceInverseConvexity.weighted_trace_inverse_convexOn`
