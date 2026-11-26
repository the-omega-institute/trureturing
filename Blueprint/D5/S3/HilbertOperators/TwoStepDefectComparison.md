# Two-step compression defect comparison

## Abstract

Two retractions onto one visible subspace give a factored difference of compression defects.

**Definition 1.1 (Two-step defect).**

Lean statement: `D5/S3/HilbertOperators/TwoStepDefectComparison.twoStepDefect`

*Formalization.* `D5/S3/HilbertOperators/TwoStepDefectComparison.twoStepDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a bounded T and inclusion i of V, the defect of R is R T² i minus (R T i)².

**Theorem 1.2 (Hidden-block factorization).**

Lean statement: `D5/S3/HilbertOperators/TwoStepDefectComparison.defect_sub_eq`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/TwoStepDefectComparison.defect_sub_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a retraction R onto V and the orthogonal projection P onto V, the defect difference equals (K W − E K) C. Here K is R restricted to the orthogonal complement, W is the hidden block of T, E is R T i, and C is the visible-to-hidden block of T. Splitting T on each return from the hidden subspace gives the identity.

**Theorem 1.3 (Centered block estimate).**

Lean statement: `D5/S3/HilbertOperators/TwoStepDefectComparison.norm_defect_sub_le`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/TwoStepDefectComparison.norm_defect_sub_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting the same complex scalar times the identity from W and E leaves K W − E K unchanged. The norm bound uses the sum of the two centered block norms, multiplied by the norms of K and C.

**Theorem 1.4 (Relative metric estimate).**

Lean statement: `D5/S3/HilbertOperators/TwoStepDefectComparison.norm_defect_sub_le_relative`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/TwoStepDefectComparison.norm_defect_sub_le_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If R is orthogonal for a symmetric coefficient between l I and u I, its hidden restriction has norm at most (u − l)/(2√(ul)) for 0 < l ≤ u. Insertion into the centered block estimate bounds the defect difference in the reference operator norm.

**Theorem 1.5 (Double-time factorization).**

Lean statement: `D5/S3/HilbertOperators/TwoStepDefectComparison.exponential_defect_sub_eq`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/TwoStepDefectComparison.exponential_defect_sub_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For T = exp(t L) and any real t, the operator exponential law identifies T² with exp(2t L) and gives the same hidden-block factorization.

**Theorem 1.6 (Bound by the centered evolution).**

Lean statement: `D5/S3/HilbertOperators/TwoStepDefectComparison.norm_defect_sub_le_sq`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/TwoStepDefectComparison.norm_defect_sub_le_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both centered blocks and the visible-to-hidden block are controlled by T − c I. The resulting defect bound is ||K|| (1 + ||R||) ||T − c I||².

**Theorem 1.7 (Quadratic small-time order).**

Lean statement: `D5/S3/HilbertOperators/TwoStepDefectComparison.exponential_defect_sub_isBigO`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/TwoStepDefectComparison.exponential_defect_sub_isBigO` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bounded complex-linear generator gives an exponential displacement of order |t| near zero. The difference of the two compression defects is therefore O(t²).

## References

- Truth anchor: `D5/S3/HilbertOperators/TwoStepDefectComparison.defect_sub_eq`
- Truth anchor: `D5/S3/HilbertOperators/TwoStepDefectComparison.exponential_defect_sub_eq`
- Truth anchor: `D5/S3/HilbertOperators/TwoStepDefectComparison.exponential_defect_sub_isBigO`
- Truth anchor: `D5/S3/HilbertOperators/TwoStepDefectComparison.norm_defect_sub_le`
- Truth anchor: `D5/S3/HilbertOperators/TwoStepDefectComparison.norm_defect_sub_le_relative`
- Truth anchor: `D5/S3/HilbertOperators/TwoStepDefectComparison.norm_defect_sub_le_sq`
- Truth anchor: `D5/S3/HilbertOperators/TwoStepDefectComparison.twoStepDefect`
- Dependency: [D5/S3/HilbertOperators/RelativeMetricProjectionStability](RelativeMetricProjectionStability.md)
