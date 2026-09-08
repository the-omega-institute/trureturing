# Balanced Truncation Tail Bounds

## Abstract

Actual principal-prefix reduction has a twice-discarded-diagonal finite-window and infinite-energy guarantee.

**Definition 1.1 (Window norm).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Euclidean norm of the finite time-output product coordinates.

**Theorem 1.2 (Window norm nonneg).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite-window Euclidean norms are nonnegative.

**Theorem 1.3 (Window norm sq).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identifies the finite-window Euclidean norm squared with the same sum-of-squares energy used in the Stein proof.

**Theorem 1.4 (Window norm zero).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A zero output window has zero norm.

**Theorem 1.5 (Window norm triangle).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applies the ordinary Euclidean triangle inequality to a telescoping output difference.

**Theorem 1.6 (Single truncation window bound).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.single_truncation_window_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationTail.single_truncation_window_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Takes nonnegative square roots of the proved finite-horizon energy bound, obtaining the two-sigma norm estimate.

**Definition 1.7 (Prefix a).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.prefixA`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationTail.prefixA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Direct principal transition block retaining exactly the first r coordinates.

**Definition 1.8 (Prefix b).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.prefixB`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationTail.prefixB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Direct input-row restriction to the first r state coordinates.

**Definition 1.9 (Prefix c).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.prefixC`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationTail.prefixC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Direct output-column restriction to the first r state coordinates.

**Definition 1.10 (Tail weight).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.tailWeight`

*Formalization.* `D5/S3/Observer/Hankel/BalancedTruncationTail.tailWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum of all discarded diagonal entries. The estimate is valid without sorting; interpreting it as a tail of exact Hankel singular values requires the separate exact-Gramian identification.

**Theorem 1.11 (Tail weight nonneg).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.tailWeight_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationTail.tailWeight_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative weights imply a nonnegative discarded sum.

**Theorem 1.12 (Tail weight self).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.tailWeight_self`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationTail.tailWeight_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Retaining all states leaves no discarded sum.

**Theorem 1.13 (Tail weight step).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.tailWeight_step`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationTail.tailWeight_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deleting the final coordinate contributes exactly its diagonal weight to the discarded sum.

**Theorem 1.14 (Balanced truncation window bound).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.balanced_truncation_window_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationTail.balanced_truncation_window_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the actual state dimension combines Stein inheritance and single-state error bounds. The resulting model is proved to be the direct principal prefix, not an arbitrary low-rank matrix. The constant is twice the entire discarded diagonal sum.

**Theorem 1.15 (Balanced truncation energy bound).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.balanced_truncation_energy_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationTail.balanced_truncation_energy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Squared finite-horizon form of the full tail-sum bound for every input window.

**Theorem 1.16 (Balanced truncation l2 bound).**

Lean statement: `D5/S3/Observer/Hankel/BalancedTruncationTail.balanced_truncation_l2_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedTruncationTail.balanced_truncation_l2_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite-energy input, bounds every error partial sum by the same total-energy budget. Mathlib monotone-series results then establish error summability and the whole-half-line bound, rather than assuming error summability.

## References

- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.balanced_truncation_energy_bound`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.balanced_truncation_l2_bound`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.balanced_truncation_window_bound`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.prefixA`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.prefixB`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.prefixC`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.single_truncation_window_bound`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.tailWeight`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.tailWeight_nonneg`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.tailWeight_self`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.tailWeight_step`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm_nonneg`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm_sq`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm_triangle`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedTruncationTail.windowNorm_zero`
- Dependency: [D5/S3/Observer/Hankel/BalancedTruncationStep](BalancedTruncationStep.md)
