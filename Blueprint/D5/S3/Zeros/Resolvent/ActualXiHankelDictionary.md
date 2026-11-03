# Finite real-polynomial Hankel identity for actual xi derivatives

## Abstract

Finite real-polynomial Hankel identity for actual xi derivatives.

**Theorem 1.1 (Finite real-polynomial Hankel identity for actual xi derivatives).**

Lean statement: `D5/S3/Zeros/Resolvent/ActualXiHankelDictionary.actual_xi_hankel_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Resolvent/ActualXiHankelDictionary.actual_xi_hankel_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural j define xiCoefficient(j) as the real part of iteratedDeriv(2j+1, xiOdd)(0) divided by (2j+1) factorial. The preceding all-order dictionary identifies it with the real actual folded moment. For arbitrary natural N and m and real coefficients indexed by Fin(N+1), put p(z) equal to their finite power polynomial.

The finite Hankel form sum over a,b of u(a) u(b) xiCoefficient(2m+a+b) equals the real part of the complete sum over actual positive-height zeros of weight times the complex square of node to power m times p(node). Finite distributivity and summable moment columns justify the equality and absolute convergence. The square is the complex algebraic square; it is never a squared norm.

With Mathlib RiemannHypothesis explicitly assumed, every node and weight is positive real, so this same finite form is nonnegative. There is no unconditional positivity or RH theorem. An off-line quadruple folds to one nonreal conjugate pair of distinct nodes; analytic multiplicity changes weights, not pair counts. No folded or full-chain negative-index count is proved here. A spectral power factor imposes no physical-space atom moment condition.

## References

- Truth anchor: `D5/S3/Zeros/Resolvent/ActualXiHankelDictionary.actual_xi_hankel_identity`
- Dependency: [D5/S3/Zeros/Resolvent/ActualXiTaylorBounds](ActualXiTaylorBounds.md)
