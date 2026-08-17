# Fibonacci Matrix Discriminant

## Abstract

The Fibonacci matrix has trace one, determinant minus one, and discriminant five.

**Theorem 1.1 (Trace, determinant, and discriminant of the Fibonacci matrix).**

$$\operatorname{tr}(M)=1 \land\ \operatorname{det}(M)=-1 \land\ \operatorname{disc}(M)=5.$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/FibonacciMatrixDiscriminant.fibonacci_substitution_trace_det_discriminant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be the existing Fibonacci substitution matrix [[1,1],[1,0]]. Its trace is 1, its determinant is -1, and its characteristic discriminant is 5.

Pinned Mathlib and Loogle were searched before formalization. The exact Fibonacci instance was not present; the proof specializes Matrix.trace_fin_two, Matrix.det_fin_two, and Matrix.discr_fin_two.

This declaration asserts only the three matrix equalities. It does not assert literal membership in SL(2,Z), which would require determinant one, nor the source's accompanying minimality interpretation.

## References

- Truth anchor: `D5/S1/Eigenstructure/FibonacciMatrixDiscriminant.fibonacci_substitution_trace_det_discriminant`
- Dependency: [D5/S1/Scale/FibonacciEigen](../Scale/FibonacciEigen.md)
