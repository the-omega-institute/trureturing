# Finite semidefinite common center

## Abstract

Universal positive-definite trace tests supply one semidefinite quadratic matrix center.

**Theorem 1.1 (One center from every positive-definite weight).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalCommonCenter.exists_common_center_of_posDef_trace_inf_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UniversalCommonCenter.exists_common_center_of_posDef_trace_inf_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r and a be finite types, with a nonempty. Let A be any complex square matrix on r times a and let B be Hermitian on the same carrier. Suppose that for every positive-definite complex matrix Z on r times a, the infimum over all complex matrices X on r of Re Tr(Z (A-X tensor I_a)(A-X tensor I_a) adjoint) is at most Re Tr(Z B). Then there exists one complex matrix X on r for which B-(A-X tensor I_a)(A-X tensor I_a) adjoint is positive semidefinite. The reference type r may be empty. There is no positivity, invertibility or normalization premise on B, and the center need not be Hermitian.

The proof works with the actual upward quadratic epigraph in the existing real Hermitian matrix space. Its convexity follows from the positive Gram remainder of a convex combination. For closedness, a convergent sequence of epigraph matrices bounds the residual trace, which bounds each residual entry. Evaluating a fixed diagonal a-coordinate bounds each center entry. Finite-dimensional compactness yields a convergent center subsequence, and the closed positive-semidefinite cone retains the limiting slack. Nonemptiness of a is used precisely in this coercivity step.

A positive-semidefinite weight is approximated by Z plus epsilon I. Nonnegative Gram trace pairings give the required monotone inequality between scalar infima; no convergence or boundedness of the weight-dependent minimizers is assumed. The existing strict Hahn-Banach separation theorem and Hermitian matrix PSD self-duality then rule out separation of zero from the epigraph.

This is a repository-derived implementation of the supplied finite semidefinite common-center inference. It is a supplier for step 3 of the original Umegaki complete-versus-conditional contraction route. Weighted quotient duality, amplified basis assembly, a common scalarizer and the final coefficient inequality remain separate unproved obligations. No novelty, solution of the original Umegaki problem, or open-problem KPI is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UniversalCommonCenter.exists_common_center_of_posDef_trace_inf_le`
