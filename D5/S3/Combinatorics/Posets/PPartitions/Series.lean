/- GID: D5/S3/Combinatorics/Posets/PPartitions/Series
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/PPartitions/Series
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown]
   utility: none
   digest: The actual descent polynomial is the bounded P-partition series numerator. -/

import D5.S3.Combinatorics.Posets.PPartitions.Counting
import Mathlib.RingTheory.PowerSeries.WellKnown

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.PPartitions

open scoped BigOperators
noncomputable section

universe u

variable {α : Type u} [Fintype α] [PartialOrder α]

/-- The finite descent enumerator is exactly the numerator of the all-bound
labelled `P`-partition generating series. -/
theorem pPartition_series (ω : α → ℕ) (hω : Function.Injective ω) :
    PowerSeries.mk (fun q => (Fintype.card (PPartition ω (q + 1)) : ℤ)) =
      (WPolynomial ω : PowerSeries ℤ) *
        (PowerSeries.invOneSubPow ℤ (Fintype.card α + 1)).val := by
  ext q
  rw [PowerSeries.coeff_mk]
  rw [pPartition_card ω hω q]
  simp only [Nat.cast_sum]
  rw [WPolynomial]
  rw [show ((∑ e : EnumeratingExtension α,
      Polynomial.X ^ descentCard ω e : Polynomial ℤ) : PowerSeries ℤ) =
      ∑ e : EnumeratingExtension α,
        ((Polynomial.X ^ descentCard ω e : Polynomial ℤ) : PowerSeries ℤ) by
          change Polynomial.coeToPowerSeries.ringHom
            (∑ e : EnumeratingExtension α, Polynomial.X ^ descentCard ω e) = _
          rw [map_sum]
          simp only [Polynomial.coeToPowerSeries.ringHom_apply,
            Polynomial.coe_pow, Polynomial.coe_X]]
  rw [Finset.sum_mul]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Polynomial.coe_pow, Polynomial.coe_X]
  rw [PowerSeries.coeff_X_pow_mul']
  rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp only [PowerSeries.coeff_mk]
  by_cases hdq : descentCard ω e ≤ q
  · rw [if_pos hdq]
    apply congrArg (fun t : ℕ => (Nat.choose t (Fintype.card α) : ℤ))
    omega
  · rw [if_neg hdq]
    simp only [Int.ofNat_eq_zero]
    apply Nat.choose_eq_zero_of_lt
    have hd : descentCard ω e ≤ Fintype.card α - 1 :=
      by simpa [descentCard] using (descentFinset ω e).card_le_univ
    omega

end

end D5.S3.Combinatorics.Posets.PPartitions
