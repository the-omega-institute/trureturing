# Positive analytic trace in every basis

## Abstract

Attributed analytic trace infrastructure, used by the original-operator quantum bridge.

**Theorem 1.1 (Positive analytic trace in every basis).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), e \in \operatorname{HilbertBasis}\left(w, H\right), T \in \operatorname{BoundedComplexOperator}\left(H\right),\; \left(\operatorname{IsTraceClass}\left(T\right) \land \operatorname{Nonnegative}\left(T\right)\right) \Rightarrow \operatorname{trace}\left(T\right) = \operatorname{tsum}\left(\left(\operatorname{inner}\left(e\left(i\right), T\left(e\left(i\right)\right)\right)\right)_{i \in w}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Basic.trace_eq_of_hilbertBasis_of_nonneg` (`✓ std3`). ∎

*Citation.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

For any positive trace-class bounded operator T on a complete complex Hilbert space, its actual analytic trace is the sum of its diagonal in any set-indexed Hilbert basis. Trace-class membership is defined through the absolute operator and summability. The finite-dimensional algebraic trace is used only in compatibility statements; the infinite-dimensional consumer uses the analytic trace.

Attributed to Tom Ole Diem, Physlib at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. The minimal five-module closure is consumed by the concrete quadratic-reference Hilbert-Schmidt bridge. This supplier adoption claims no mathematical originality. An equivalent consumed result at the repository-pinned Mathlib replaces the transplant.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Basic.trace_eq_of_hilbertBasis_of_nonneg`
