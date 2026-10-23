# Cyclicity with a bounded factor

## Abstract

Analytic trace norms and bounded trace pairings on arbitrary complete complex Hilbert spaces.

**Theorem 1.1 (Cyclicity with a bounded factor).**

$$\forall H \in CompleteComplexHilbertSpace, A \in \operatorname{BoundedComplexOperator}\left(H\right), T \in \operatorname{BoundedComplexOperator}\left(H\right),\; \operatorname{IsTraceClass}\left(T\right) \Rightarrow \operatorname{trace}\left(\operatorname{mul}\left(A, T\right)\right) = \operatorname{trace}\left(\operatorname{mul}\left(T, A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/TraceAlgebra.trace_mul_cycle` (`✓ std3`). ∎

*Citation.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

For a bounded A and an actual trace-class T, the analytic traces of A T and T A agree. Scalar homogeneity and additivity use the basis-independent absolutely summable diagonals. No finite-dimensional algebraic trace is substituted.

Attributed to Tom Ole Diem, Physlib at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. The original copyright notice and license are preserved. No mathematical originality is claimed for these suppliers.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/TraceAlgebra.trace_mul_cycle`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Banach](Banach.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/IdealNorm](IdealNorm.md)
