# Hilbert-Schmidt and trace-class compactness

## Abstract

Finite Hilbert-basis approximations and compactness in the operator norm.

**Theorem 1.1 (Column bound).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, H\right), S \in \operatorname{BoundedComplexOperator}\left(H\right),\; \operatorname{Summable}\left(\operatorname{square}\left(\operatorname{norm}\left(S\left(b\left(i\right)\right)\right)\right)iw\right) \Rightarrow \operatorname{norm}\left(S\right) \le \operatorname{sqrt}\left(\operatorname{tsum}\left(\operatorname{square}\left(\operatorname{norm}\left(S\left(b\left(i\right)\right)\right)\right)iw\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Compact.opNorm_le_sqrt_column_square_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

A continuous operator with square-summable basis columns equals the synthesized operator on the dense basis span. Thus its actual operator norm is bounded by the square root of the column square sum.

**Definition 1.2 (Finite column approximation).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, H\right), S \in \operatorname{BoundedComplexOperator}\left(H\right), F \in \operatorname{Finset}\left(w\right),\; \operatorname{finiteColumnApprox}\left(b, S, F\right) = \operatorname{compose}\left(S, \operatorname{basisProjection}\left(b, F\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/TraceClass/Compact.finiteColumnApprox` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

P_F is the existing Hilbert-basis Schauder projection onto the finite span of b(F). The approximation is S composed with P_F.

**Definition 1.3 (Complement column square sum).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, H\right), S \in \operatorname{BoundedComplexOperator}\left(H\right), F \in \operatorname{Finset}\left(w\right),\; \operatorname{tailColumnSquareSum}\left(b, S, F\right) = \operatorname{tsum}\left(\operatorname{square}\left(\operatorname{norm}\left(S\left(b\left(i\right)\right)\right)\right)i\operatorname{complementSubtype}\left(w, F\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/TraceClass/Compact.tailColumnSquareSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

The tail is the real sum over the complement subtype of F, including every zero column.

**Theorem 1.4 (Projection columns).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, H\right), S \in \operatorname{BoundedComplexOperator}\left(H\right), F \in \operatorname{Finset}\left(w\right),\; \forall i \in w,\; \operatorname{finiteColumnApprox}\left(b, S, F\right)\left(b\left(i\right)\right) = \operatorname{if}\left(\operatorname{member}\left(i, F\right), S\left(b\left(i\right)\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Compact.finiteColumnApprox_apply_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

On a selected basis vector the approximation agrees with S, and on every other basis vector it is zero.

**Theorem 1.5 (Compact approximants).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, H\right), S \in \operatorname{BoundedComplexOperator}\left(H\right), F \in \operatorname{Finset}\left(w\right),\; \operatorname{IsCompactOperator}\left(\operatorname{finiteColumnApprox}\left(b, S, F\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Compact.isCompactOperator_finiteColumnApprox` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

The projection's actual range equals the span of the finite image b(F), so that range is finite-dimensional and locally compact. Restriction to this range is compact, and continuous postcomposition by the inclusion and S gives the approximation.

**Theorem 1.6 (Uniform norm tail).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, H\right), S \in \operatorname{BoundedComplexOperator}\left(H\right), F \in \operatorname{Finset}\left(w\right),\; \operatorname{Summable}\left(\operatorname{square}\left(\operatorname{norm}\left(S\left(b\left(i\right)\right)\right)\right)iw\right) \Rightarrow \operatorname{norm}\left(\operatorname{subtract}\left(S, \operatorname{finiteColumnApprox}\left(b, S, F\right)\right)\right) \le \operatorname{sqrt}\left(\operatorname{tailColumnSquareSum}\left(b, S, F\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Compact.norm_sub_finiteColumnApprox_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

Residual columns vanish on F and equal S(b_i) off F. Their square sum is summable and equals the complement-subtype tail. Applying the column synthesis bound to this residual proves a uniform operator norm estimate on all vectors.

**Theorem 1.7 (Squared norm tail).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, H\right), S \in \operatorname{BoundedComplexOperator}\left(H\right), F \in \operatorname{Finset}\left(w\right),\; \operatorname{Summable}\left(\operatorname{square}\left(\operatorname{norm}\left(S\left(b\left(i\right)\right)\right)\right)iw\right) \Rightarrow \operatorname{square}\left(\operatorname{norm}\left(\operatorname{subtract}\left(S, \operatorname{finiteColumnApprox}\left(b, S, F\right)\right)\right)\right) \le \operatorname{tailColumnSquareSum}\left(b, S, F\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Compact.norm_sub_finiteColumnApprox_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

The nonnegative tail permits squaring the norm estimate.

**Theorem 1.8 (Operator norm convergence).**

$$\forall H \in CompleteComplexHilbertSpace, w \in \operatorname{Set}\left(H\right), b \in \operatorname{HilbertBasis}\left(w, H\right), S \in \operatorname{BoundedComplexOperator}\left(H\right),\; \operatorname{Summable}\left(\operatorname{square}\left(\operatorname{norm}\left(S\left(b\left(i\right)\right)\right)\right)iw\right) \Rightarrow \operatorname{Tendsto}\left(\operatorname{finiteColumnApprox}\left(b, S\right), \operatorname{atTop}\left(\operatorname{Finset}\left(w\right)\right), \operatorname{nhds}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Compact.tendsto_finiteColumnApprox` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

The directed index is all finite subsets of w, ordered by inclusion. Summable complement tails tend to zero, so the squared residual norms and then their square roots tend to zero. This proves convergence in the normed continuous-linear-map space, without selecting a sequence or using only pointwise convergence.

**Theorem 1.9 (Hilbert-Schmidt compactness).**

$$\forall H \in CompleteComplexHilbertSpace, S \in \operatorname{BoundedComplexOperator}\left(H\right),\; \operatorname{IsHilbertSchmidt}\left(S\right) \Rightarrow \operatorname{IsCompactOperator}\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Compact.isCompactOperator_of_isHilbertSchmidt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

Unpack the arbitrary set-indexed Hilbert basis in the Hilbert-Schmidt premise. Every finite column approximation is compact, and the norm limit is compact because H is complete.

**Theorem 1.10 (Positive trace-class compactness).**

$$\forall H \in CompleteComplexHilbertSpace, S \in \operatorname{BoundedComplexOperator}\left(H\right),\; \left(\operatorname{IsTraceClass}\left(S\right) \land 0 \le S\right) \Rightarrow \operatorname{IsCompactOperator}\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Compact.isCompactOperator_of_nonneg_isTraceClass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

For positive T the actual CFC square root is Hilbert-Schmidt and compact. Its square equals T, and composition with a continuous operator preserves compactness.

**Theorem 1.11 (General trace-class compactness).**

$$\forall H \in CompleteComplexHilbertSpace, S \in \operatorname{BoundedComplexOperator}\left(H\right),\; \operatorname{IsTraceClass}\left(S\right) \Rightarrow \operatorname{IsCompactOperator}\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TraceClass/Compact.isCompactOperator_of_isTraceClass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tom Ole Diem (2026). *Analytic trace-class and Hilbert-Schmidt operators*. URL: <https://github.com/leanprover-community/physlib/tree/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/PhyslibAlpha/AlgebraicFramework/HilbertSpace/TraceClass>.

*Commentary.*

The positive absolute value of any trace-class T is trace class and compact. The actual bounded polar factor multiplied by this absolute value equals T, so T is compact. Self-adjointness is unnecessary.

All statements retain arbitrary complete complex Hilbert spaces and arbitrary set-indexed Hilbert bases. They require no separability, injectivity, finite ambient dimension or eigenbasis. The trace-class predicate and CFC/polar suppliers are the attributed Physlib analytic infrastructure. These compactness statements supply a premise for later spectral arguments; no complete spectral basis or common energy and heat-trace conclusion follows here.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Compact.finiteColumnApprox`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Compact.finiteColumnApprox_apply_basis`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Compact.isCompactOperator_finiteColumnApprox`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Compact.isCompactOperator_of_isHilbertSchmidt`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Compact.isCompactOperator_of_isTraceClass`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Compact.isCompactOperator_of_nonneg_isTraceClass`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Compact.norm_sub_finiteColumnApprox_le`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Compact.norm_sub_finiteColumnApprox_sq_le`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Compact.opNorm_le_sqrt_column_square_sum`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Compact.tailColumnSquareSum`
- Truth anchor: `D5/S3/Quantum/Analysis/TraceClass/Compact.tendsto_finiteColumnApprox`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/ColumnSynthesis](ColumnSynthesis.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/GeneralIdeal](GeneralIdeal.md)
