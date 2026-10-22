# Complete finite-head tail kernel at every cutoff

## Abstract

Complete finite-head tail kernel at every cutoff

For every natural c>=3, finite integer head S, natural cutoff N and complex coefficient function v, the complete paired tail energy vanishes exactly when v vanishes on S. The empty head and zero vector are included.

ActualUniformFiniteHeadTail.actual_finite_head_uniform_tail_lower provides the coefficient-uniform lower bound for c>=2: positive C and a cutoff N0 are chosen before all coefficient functions and all later cutoffs. Its summability at N+N0, reindexing of both signed columns and Summable.comp_nat_add give summability at every N.

A retained nonzero coefficient gives strictly positive original coefficient mass. The uniform lower bound gives a positive complete tail at max(N,N0), and nonnegative tail cropping transfers positivity to N. This is a consequence of the uniform estimate; ActualThreeNodeSourceHeadBridge uses that consequence on the literal three-node head.

**Theorem 1.1 (actual tail summable all).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel.actual_tail_summable_all`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel.actual_tail_summable_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_tail_summable_all {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (hS : S.Nonempty) (N : ℕ) (v : ℤ → ℂ) : Summable (pairedColumnTerm c N S v)

**Theorem 1.2 (actual finite head tail pos).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel.actual_finite_head_tail_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel.actual_finite_head_tail_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_finite_head_tail_pos {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) (hv : ∃ k ∈ S, v k ≠ 0) : 0 < ∑' j : ℕ, pairedColumnTerm c N S v j

**Theorem 1.3 (actual finite head tail zero iff).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel.actual_finite_head_tail_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel.actual_finite_head_tail_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_finite_head_tail_zero_iff {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) : (∑' j : ℕ, pairedColumnTerm c N S v j) = 0 ↔ ∀ k ∈ S, v k = 0

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel.actual_finite_head_tail_pos`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel.actual_finite_head_tail_zero_iff`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel.actual_tail_summable_all`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualNodalTailEnclosure](ActualNodalTailEnclosure.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualUniformFiniteHeadTail](ActualUniformFiniteHeadTail.md)
