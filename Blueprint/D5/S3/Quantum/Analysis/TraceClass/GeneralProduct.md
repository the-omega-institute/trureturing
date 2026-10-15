# The actual trace-class product and ideal

## Abstract

Attributed analytic trace infrastructure, used by the original-operator quantum bridge.

**Theorem 1.1 (The actual trace-class product and ideal).**

$$\forall H \in CompleteComplexHilbertSpace, R \in \operatorname{BoundedComplexOperator}\left(H\right), S \in \operatorname{BoundedComplexOperator}\left(H\right),\; \left(\operatorname{IsHilbertSchmidt}\left(R\right) \land \operatorname{IsHilbertSchmidt}\left(S\right)\right) \Rightarrow \operatorname{IsTraceClass}\left(R \cdot S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/GeneralProduct.isTraceClass_mul_of_isHilbertSchmidt` (`✓ std3`). ∎

*Citation.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

For two arbitrary Hilbert-Schmidt bounded operators R and S on a complete complex Hilbert space, their product is trace class. The supplied proof uses the general polar factor and the supplied scalar square-sum estimate. Its two-sided bounded ideal consequence is used to form the original analytic traces in the quantum bridge.

Attributed to Tom Ole Diem, Physlib at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. The minimal five-module closure is consumed by the concrete quadratic-reference Hilbert-Schmidt bridge. This supplier adoption claims no mathematical originality. An equivalent consumed result at the repository-pinned Mathlib replaces the transplant.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/GeneralProduct.isTraceClass_mul_of_isHilbertSchmidt`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/GeneralIdeal](GeneralIdeal.md)
