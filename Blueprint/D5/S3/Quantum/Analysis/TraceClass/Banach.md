# The genuine trace-class Banach space

## Abstract

Analytic trace norms and bounded trace pairings on arbitrary complete complex Hilbert spaces.

**Theorem 1.1 (The genuine trace-class Banach space).**

$$\forall H \in CompleteComplexHilbertSpace, Tn \in \operatorname{Sequence}\left(\operatorname{BoundedComplexOperator}\left(H\right)\right), T \in \operatorname{BoundedComplexOperator}\left(H\right), C \in Real,\; \left(\operatorname{EachTraceClass}\left(Tn\right) \land \left(\operatorname{UniformTraceNormBound}\left(Tn, C\right) \land \operatorname{TendstoOperatorNorm}\left(Tn, T\right)\right)\right) \Rightarrow \left(\operatorname{IsTraceClass}\left(T\right) \land \operatorname{traceNorm}\left(T\right) \le C\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Banach.isTraceClass_of_tendsto_of_traceNorm_bounded` (`✓ std3`). ∎

*Citation.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

The trace norm equips the trace-class submodule with a complete complex normed-space structure. The operator norm is bounded by the trace norm. Uniformly trace-norm-bounded operator-norm limits are trace class with the same bound; this supplies the completeness proof.

Attributed to Tom Ole Diem, Physlib at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. The original copyright notice and license are preserved. No mathematical originality is claimed for these suppliers.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Banach.isTraceClass_of_tendsto_of_traceNorm_bounded`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Basic](Basic.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/GeneralProduct](GeneralProduct.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/IdealNorm](IdealNorm.md)
