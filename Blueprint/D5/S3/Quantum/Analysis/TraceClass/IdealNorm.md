# The two-sided trace-norm ideal estimate

## Abstract

Analytic trace norms and bounded trace pairings on arbitrary complete complex Hilbert spaces.

**Theorem 1.1 (The two-sided trace-norm ideal estimate).**

$$\forall H \in CompleteComplexHilbertSpace, A \in \operatorname{BoundedComplexOperator}\left(H\right), T \in \operatorname{BoundedComplexOperator}\left(H\right), B \in \operatorname{BoundedComplexOperator}\left(H\right),\; \left(\operatorname{IsTraceClass}\left(T\right) \land \operatorname{IsTraceClass}\left(\operatorname{mul}\left(\operatorname{mul}\left(A, T\right), B\right)\right)\right) \Rightarrow \operatorname{traceNorm}\left(\operatorname{mul}\left(\operatorname{mul}\left(A, T\right), B\right)\right) \le \operatorname{mul}\left(\operatorname{mul}\left(\operatorname{norm}\left(A\right), \operatorname{traceNorm}\left(T\right)\right), \operatorname{norm}\left(B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/IdealNorm.traceNorm_mul_mul_le` (`✓ std3`). ∎

*Citation.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

For arbitrary bounded A and B and an actual trace-class T, the operator A T B is trace class and has trace norm at most the product of the operator norms of A and B and the trace norm of T. The supplied proof uses polar factorization and the Hilbert-Schmidt product estimate.

Attributed to Tom Ole Diem, Physlib at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. The original copyright notice and license are preserved. No mathematical originality is claimed for these suppliers.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/IdealNorm.traceNorm_mul_mul_le`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/GeneralProduct](GeneralProduct.md)
