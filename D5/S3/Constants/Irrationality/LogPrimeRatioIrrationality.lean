/- GID: D5/S3/Constants/Irrationality/LogPrimeRatioIrrationality
   generality: I
   mirror-B: D5/B/S3/Constants/Irrationality/LogPrimeRatioIrrationality
   mirror-E: none(waiver:elementary-number-theory)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.Irrational]
   utility: none
   digest: Elementary independence of the logarithms of two and three. -/
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! UNCOMPILED_UNACCEPTED. Prime-power arithmetic, with no transcendence input. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Constants.Irrationality.LogPrimeRatioIrrationality
open Real

/-- The ratio, rather than the individual logarithms, is irrational. -/
theorem irrational_log_three_div_log_two : Irrational (log 3 / log 2) := by
  rintro ⟨q, hq⟩
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have h3 : 0 < log (3 : ℝ) := log_pos (by norm_num)
  have hqpos : (0 : ℚ) < q := by
    have : (0 : ℝ) < (q : ℝ) := by rw [hq]; exact div_pos h3 h2
    exact_mod_cast this
  have hn : 0 < q.num := Rat.num_pos.mpr hqpos
  have hd : 0 < q.den := q.pos
  have hcast : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn.le
  have hlin : (q.den : ℝ) * log 3 = (q.num.toNat : ℝ) * log 2 := by
    rw [Rat.cast_def] at hq
    have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [hcast]
    field_simp [h2.ne', hden] at hq
    nlinarith only [hq]
  have hlogs : log ((3 : ℝ) ^ q.den) = log ((2 : ℝ) ^ q.num.toNat) := by
    simpa only [log_pow] using hlin
  have hpowers : (3 : ℝ) ^ q.den = (2 : ℝ) ^ q.num.toNat :=
    strictMonoOn_log.injOn (show 0 < (3 : ℝ) ^ q.den by positivity)
      (show 0 < (2 : ℝ) ^ q.num.toNat by positivity) hlogs
  have hnat : (3 : ℕ) ^ q.den = (2 : ℕ) ^ q.num.toNat := by exact_mod_cast hpowers
  have hdiv : 3 ∣ (2 : ℕ) ^ q.num.toNat := by
    rw [← hnat]
    obtain ⟨d, hd'⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    rw [hd']
    exact ⟨3 ^ d, by simp [pow_succ, mul_comm]⟩
  have : 3 ∣ (2 : ℕ) := (by norm_num : Nat.Prime 3).dvd_of_dvd_pow hdiv
  norm_num at this

#print axioms irrational_log_three_div_log_two
end D5.S3.Constants.Irrationality.LogPrimeRatioIrrationality
