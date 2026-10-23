# Analytic trace in an arbitrary basis

## Abstract

Attributed analytic trace infrastructure, used by the original-operator quantum bridge.

**Theorem 1.1 (Analytic trace in an arbitrary basis).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), e \in \operatorname{HilbertBasis}\left(w, H\right), T \in \operatorname{BoundedComplexOperator}\left(H\right),\; \operatorname{IsTraceClass}\left(T\right) \Rightarrow \operatorname{trace}\left(T\right) = \operatorname{tsum}\left(\left(\operatorname{inner}\left(e\left(i\right), T\left(e\left(i\right)\right)\right)\right)_{i \in w}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/GeneralIdeal.trace_eq_of_hilbertBasis` (`✓ std3`). ∎

*Citation.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

For every trace-class bounded operator T and every set-indexed Hilbert basis e, the genuine trace of T equals the convergent sum of inner products of e of i with T applied to e of i. No positivity or self-adjointness premise on T is required. The consumer uses this for the original products rho B and sigma B squared.

Attributed to Tom Ole Diem, Physlib at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. The minimal five-module closure is consumed by the concrete quadratic-reference Hilbert-Schmidt bridge. This supplier adoption claims no mathematical originality. An equivalent consumed result at the repository-pinned Mathlib replaces the transplant.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/GeneralIdeal.trace_eq_of_hilbertBasis`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/HilbertSchmidt](HilbertSchmidt.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Polar](Polar.md)
