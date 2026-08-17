/- GID: D5/S3/Quantum/Sharpness/SpectralSharpnessDuality
   generality: G
   mirror-B: D5/B/S3/Quantum/Sharpness/SpectralSharpnessDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Spectral sharpness is the attained maximum of bounded spectral pairings. -/

import D5.S3.Quantum.Sharpness.SpectralPairingCapacity
import D5.S3.Quantum.Sharpness.SpectralSharpness

namespace D5.S3.Quantum.Sharpness.SpectralSharpnessDuality

open Finset
open D5.S3.Quantum.Sharpness.SpectralPairingCapacity
open D5.S3.Quantum.Sharpness.SpectralSharpness

private theorem spectralPairingCapacity_eq_signedPairing {n : ℕ}
    (r a : Fin n → ℝ) :
    spectralPairingCapacity r a =
      (1 / 2 : ℝ) * ∑ i, (r i - r (Fin.rev i)) * a i := by
  unfold spectralPairingCapacity
  congr 1
  calc
    ∑ i, r i * (a i - a (Fin.rev i)) =
        ∑ i, (r i * a i - r i * a (Fin.rev i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, r i * a i) - ∑ i, r i * a (Fin.rev i) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ i, r i * a i) - ∑ i, r (Fin.rev i) * a i := by
      congr 1
      simpa using
        (Equiv.sum_comp Fin.revPerm (fun i => r (Fin.rev i) * a i))
    _ = ∑ i, (r i - r (Fin.rev i)) * a i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Spectral sharpness is the greatest spectral pairing against an observable whose coordinates
have absolute value at most one. The greatest value is attained by the sign of the difference
between the spectrum and its reversal. -/
theorem spectral_sharpness_isGreatest_bounded_pairing {n : ℕ} (r : Fin n → ℝ) :
    IsGreatest
      {value : ℝ | ∃ a : Fin n → ℝ, (∀ i, |a i| ≤ 1) ∧
        spectralPairingCapacity r a = value}
      (spectralSharpness r) := by
  constructor
  · let a : Fin n → ℝ := fun i =>
      if 0 ≤ r i - r (Fin.rev i) then 1 else -1
    refine ⟨a, ?_, ?_⟩
    · intro i
      by_cases h : 0 ≤ r i - r (Fin.rev i)
      · simp only [a, if_pos h, abs_one, le_refl]
      · simp only [a, if_neg h, abs_neg, abs_one, le_refl]
    · rw [spectralPairingCapacity_eq_signedPairing, spectralSharpness]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : 0 ≤ r i - r (Fin.rev i)
      · simp only [a, if_pos h, mul_one, abs_of_nonneg h]
      · have hneg : r i - r (Fin.rev i) < 0 := lt_of_not_ge h
        simp only [a, if_neg h, mul_neg, mul_one, abs_of_neg hneg]
  · rintro value ⟨a, ha, rfl⟩
    rw [spectralPairingCapacity_eq_signedPairing, spectralSharpness]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro i _
    calc
      (r i - r (Fin.rev i)) * a i ≤ |(r i - r (Fin.rev i)) * a i| :=
        le_abs_self _
      _ = |r i - r (Fin.rev i)| * |a i| := abs_mul _ _
      _ ≤ |r i - r (Fin.rev i)| * 1 :=
        mul_le_mul_of_nonneg_left (ha i) (abs_nonneg _)
      _ = |r i - r (Fin.rev i)| := mul_one _

end D5.S3.Quantum.Sharpness.SpectralSharpnessDuality
