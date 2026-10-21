# Finite arithmetic heads and complete tail energy

## Abstract

Finite arithmetic heads and complete tail energy

For every natural c>=3, finite integer head S, natural cutoff N and complex coefficient function v, the complete paired tail energy is zero exactly when v vanishes on S. The empty head and zero vector are included; values outside S play no role.

The positive mean square of the actual prime symbol controls the reciprocal Q energy. The nodal reconstruction formula makes Q nonzero whenever a retained coefficient is nonzero. Reversal and dilation preserve this property at a positive cutoff.

The explicit 336 uniform enclosure chooses a cutoff before the coefficient vector. Its lower inequality gives positive energy without dividing by an energy or a coefficient mass. Nonnegative tail cropping then transfers positivity to every original cutoff, including zero.

This concerns the actual arithmetic divided-difference columns. It gives neither injectivity on all integer-indexed functions nor a uniform positive constant independent of cutoff. It does not identify the full physical Weil operator or assert RH or Robin.

**Theorem 1.1 (actual tail summable all).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy.actual_tail_summable_all`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy.actual_tail_summable_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_tail_summable_all {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (hS : S.Nonempty) (N : ℕ) (v : ℤ → ℂ) : Summable (pairedColumnTerm c N S v)

**Theorem 1.2 (actual finite head tail pos).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy.actual_finite_head_tail_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy.actual_finite_head_tail_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_finite_head_tail_pos {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) (hv : ∃ k ∈ S, v k ≠ 0) : 0 < ∑' j : ℕ, pairedColumnTerm c N S v j

**Theorem 1.3 (actual finite head tail zero iff).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy.actual_finite_head_tail_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy.actual_finite_head_tail_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_finite_head_tail_zero_iff {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) : (∑' j : ℕ, pairedColumnTerm c N S v j) = 0 ↔ ∀ k ∈ S, v k = 0

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy.actual_finite_head_tail_pos`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy.actual_finite_head_tail_zero_iff`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy.actual_tail_summable_all`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualExplicit336](ActualExplicit336.md)
