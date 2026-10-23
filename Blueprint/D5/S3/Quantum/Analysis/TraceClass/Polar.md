# Actual polar factorization

## Abstract

Attributed analytic trace infrastructure, used by the original-operator quantum bridge.

**Theorem 1.1 (Actual polar factorization).**

$$\forall H \in CompleteComplexHilbertSpace, T \in \operatorname{BoundedComplexOperator}\left(H\right),\; \operatorname{polarFactor}\left(T\right) \cdot \operatorname{absOperator}\left(T\right) = T$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Polar.polarFactor_mul_absOperator` (`✓ std3`). ∎

*Citation.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

For every bounded operator T on a complete complex Hilbert space, the supplied contraction polarFactor of T multiplied by the actual continuous-functional-calculus absolute operator is T. No invertibility, closed range, finite dimension, or self-adjointness premise is introduced.

Attributed to Tom Ole Diem, Physlib at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. The minimal five-module closure is consumed by the concrete quadratic-reference Hilbert-Schmidt bridge. This supplier adoption claims no mathematical originality. An equivalent consumed result at the repository-pinned Mathlib replaces the transplant.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Polar.polarFactor_mul_absOperator`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Basic](Basic.md)
