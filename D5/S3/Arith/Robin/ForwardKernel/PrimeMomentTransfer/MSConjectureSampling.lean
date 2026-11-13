/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureSampling
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MSConjectureSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth moment control removes terminal cell losses on all sublinear bands. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthMoments
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthBandGeometry
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.UniformRates
import D5.S3.Arith.Robin.ForwardKernel.FourthMomentBandDefs

/-! Continuous prime moment bounds without a long terminal-cell loss. -/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
open VarianceTransferDefs FourthMomentBandDefs
noncomputable section
set_option autoImplicit false

/-- A fourth moment bounds the omitted terminal cell in the second moment. -/
private theorem terminal_second_of_fourth (A Y v t : ℝ)
    (hY : 2 ≤ Y) (hv : 1 ≤ v) (ht : 0 ≤ t) (hAY : A ≤ t ^ 2 * Y)
    (hfour : discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ A * Y * (v * Real.log Y) ^ 2) :
    |(∫ x in (1 : ℝ)..Y, primeIncrement (⌊v⌋₊ : ℝ) (⌊x⌋₊ : ℝ) ^ 2) -
      discretePrimeMoment 2 ⌊Y⌋₊ ⌊v⌋₊| ≤ t * Y * (v * Real.log Y) := by
  have hY0 : 0 ≤ Y := by linarith
  have hq : 0 ≤ v * Real.log Y := mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  have hN : ⌊Y⌋₊ ∈ Finset.Ioc 0 ⌊Y⌋₊ := by
    simp only [Finset.mem_Ioc, le_refl, and_true]
    exact lt_of_lt_of_le (by norm_num : 0 < 2) (Nat.le_floor (by simpa using hY))
  have hcell : primeIncrement (⌊v⌋₊ : ℝ) (⌊Y⌋₊ : ℝ) ^ 4 ≤
      discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ :=
    by
      unfold discretePrimeMoment
      exact Finset.single_le_sum (f := fun n : ℕ => primeIncrement (⌊v⌋₊ : ℝ) (n : ℝ) ^ 4)
        (fun n _ => by positivity) hN
  have hcell' : (primeIncrement (⌊v⌋₊ : ℝ) (⌊Y⌋₊ : ℝ) ^ 2) ^ 2 ≤
      (t * Y * (v * Real.log Y)) ^ 2 := by
    calc
      _ = primeIncrement (⌊v⌋₊ : ℝ) (⌊Y⌋₊ : ℝ) ^ 4 := by ring
      _ ≤ A * Y * (v * Real.log Y) ^ 2 := hcell.trans hfour
      _ ≤ (t ^ 2 * Y) * Y * (v * Real.log Y) ^ 2 := by gcongr
      _ = _ := by ring
  have hp : primeIncrement (⌊v⌋₊ : ℝ) (⌊Y⌋₊ : ℝ) ^ 2 ≤
      t * Y * (v * Real.log Y) :=
    (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp hcell'
  have hi := floor_integral_identity (fun n => primeIncrement (⌊v⌋₊ : ℝ) (n : ℝ) ^ 2)
    Y (by linarith)
  have hc : |Y - (⌊Y⌋₊ : ℝ) - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Nat.floor_le hY0, Nat.lt_floor_add_one Y]
  change |(∫ x in (1 : ℝ)..Y, primeIncrement (⌊v⌋₊ : ℝ) (⌊x⌋₊ : ℝ) ^ 2) -
    (∑ n ∈ Finset.Ioc 0 ⌊Y⌋₊, primeIncrement (⌊v⌋₊ : ℝ) (n : ℝ) ^ 2)| ≤ _
  rw [hi, abs_mul]
  rw [abs_of_nonneg (sq_nonneg (primeIncrement (⌊v⌋₊ : ℝ) (⌊Y⌋₊ : ℝ)))]
  exact (mul_le_of_le_one_left (sq_nonneg _) hc).trans hp

/-- On every positive polynomial band, the prefix replacement has vanishing second moment error. -/
private theorem prefix_second_uniform (α β A η : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) (hA : 1 ≤ A) (hη : 0 < η)
    (hfour : ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ A * Y * v ^ 2 * Real.log Y ^ 2) :
    ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      |continuousPrimeMoment 2 Y v -
        (∫ x in (1 : ℝ)..Y, primeIncrement (⌊v⌋₊ : ℝ) (⌊x⌋₊ : ℝ) ^ 2)| ≤
          η * Y * v * Real.log (Y / v) := by
  let t := min 1 (η * (1 - β) / (3520 * (1 + A)))
  have ht : 0 < t := lt_min zero_lt_one (by positivity)
  filter_upwards [hfour, sqrt_rate α t hα ht, eventually_ge_atTop (2 : ℝ)]
    with Y hfour hs hY v hvα hvβ
  obtain ⟨hv, hvY⟩ := FourthTransfer.FourthMomentAsymptotic.band_lengths
    (by linarith : 1 ≤ Y) hα hαβ hβ hvα hvβ
  have hs0 : 0 ≤ Real.sqrt (Real.log Y / v) := Real.sqrt_nonneg _
  have hst := hs v hvα
  have hs1 : Real.sqrt (Real.log Y / v) ≤ 1 := hst.trans (min_le_left _ _)
  have hsq : Real.sqrt (Real.log Y / v) ^ 2 ≤ Real.sqrt (Real.log Y / v) := by
    nlinarith only [hs0, hs1]
  have hraw := sampling_prefix_estimate 2 (Or.inl rfl) A Y v hA hY hv hvY
    (hfour v hvα hvβ)
  have hq : Real.sqrt (v * Real.log Y) ^ 2 = v * Real.log Y :=
    Real.sq_sqrt (mul_nonneg (by linarith) (Real.log_nonneg (by linarith)))
  rw [hq] at hraw
  have hsmall : 10 * Real.sqrt (Real.log Y / v) +
      (10 * Real.sqrt (Real.log Y / v)) ^ 2 ≤
      110 * (η * (1 - β) / (3520 * (1 + A))) := by
    have htη := hst.trans (min_le_right _ _)
    nlinarith only [hsq, htη]
  have hbound := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ 32 * (1 + A) * Y * (v * Real.log Y) by
      positivity [Real.log_nonneg (by linarith : 1 ≤ Y)])
  have hid : 32 * (1 + A) * Y * (v * Real.log Y) *
      (110 * (η * (1 - β) / (3520 * (1 + A)))) =
      η * Y * v * ((1 - β) * Real.log Y) := by
    have hAp : 1 + A ≠ 0 := ne_of_gt (by linarith)
    field_simp [hAp]
    ring
  rw [hid] at hbound
  exact hraw.trans (hbound.trans (mul_le_mul_of_nonneg_left
    (band_log β Y v hβ (by linarith) hv hvβ).2.1 (by positivity)))

/-- A uniform discrete fourth bound gives asymptotically exact second moment sampling
on any sublinear polynomial length band. -/
theorem second_sampling_uniform_of_fourth (α β A : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) (hA : 1 ≤ A)
    (hfour : ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ A * Y * v ^ 2 * Real.log Y ^ 2)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      |continuousPrimeMoment 2 Y v - discretePrimeMoment 2 ⌊Y⌋₊ ⌊v⌋₊| ≤
        η * Y * v * Real.log (Y / v) := by
  let t := (η / 2) * (1 - β)
  have ht : 0 < t := by dsimp [t]; positivity
  filter_upwards [prefix_second_uniform α β A (η / 2) hα hαβ hβ hA (half_pos hη) hfour,
    hfour, eventually_ge_atTop (max 2 (A / t ^ 2))] with Y hprefix hfour hY v hvα hvβ
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  obtain ⟨hv, _⟩ := FourthTransfer.FourthMomentAsymptotic.band_lengths
    (by linarith : 1 ≤ Y) hα hαβ hβ hvα hvβ
  have hAY : A ≤ t ^ 2 * Y := by
    have h := (le_max_right 2 (A / t ^ 2)).trans hY
    exact (div_le_iff₀ (sq_pos_of_pos ht)).mp h |>.trans_eq (mul_comm _ _)
  have hfour' : discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ A * Y * (v * Real.log Y) ^ 2 := by
    simpa only [mul_pow, mul_assoc] using hfour v hvα hvβ
  have hterm := terminal_second_of_fourth A Y v t hY2 hv ht.le hAY hfour'
  have hl := (band_log β Y v hβ (by linarith) hv hvβ).2.1
  have htbound : t * Y * (v * Real.log Y) ≤ (η / 2) * Y * v * Real.log (Y / v) := by
    calc
      _ = (η / 2) * Y * v * ((1 - β) * Real.log Y) := by dsimp [t]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  exact (abs_sub_le _ _ _).trans (by linarith only [hprefix v hvα hvβ, hterm.trans htbound])

/-- A discrete fourth bound yields the existing continuous fourth moment predicate
on every sublinear exponent band. -/
theorem fourth_band_bound_of_discrete (α β A : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) (hA : 1 ≤ A)
    (hfour : ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ A * Y * v ^ 2 * Real.log Y ^ 2) :
    ∃ C₄ : ℝ, FourthMomentBandBoundFor chebyshevError α β C₄ := by
  let C := A + 320320 * (1 + A)
  have hC : 0 ≤ C := by dsimp [C]; linarith only [hA]
  refine ⟨C / (1 - β) ^ 2, div_nonneg hC (sq_nonneg _), ?_⟩
  filter_upwards [hfour, sqrt_rate α 1 hα zero_lt_one,
    eventually_ge_atTop (2 : ℝ)]
    with Y hfour hs hY v hvα hvβ
  obtain ⟨hv, hvY⟩ := FourthTransfer.FourthMomentAsymptotic.band_lengths
    (by linarith : 1 ≤ Y) hα hαβ hβ hvα hvβ
  have hL : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hs0 : 0 ≤ Real.sqrt (Real.log Y / v) := Real.sqrt_nonneg _
  have hs1 := hs v hvα
  have hs4 : Real.sqrt (Real.log Y / v) ^ 4 ≤ 1 := pow_le_one₀ hs0 hs1
  have hrate : 10 * Real.sqrt (Real.log Y / v) +
      (10 * Real.sqrt (Real.log Y / v)) ^ 4 ≤ 10010 := by
    nlinarith only [hs1, hs4]
  have hraw := sampling_prefix_estimate 4 (Or.inr rfl) A Y v hA hY hv hvY
    (hfour v hvα hvβ)
  have hq : Real.sqrt (v * Real.log Y) ^ 4 = v ^ 2 * Real.log Y ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (mul_nonneg (by linarith) hL), mul_pow]
  rw [hq] at hraw
  have hstep : (∫ x in (1 : ℝ)..Y, primeIncrement (⌊v⌋₊ : ℝ) (⌊x⌋₊ : ℝ) ^ 4) ≤
      A * Y * v ^ 2 * Real.log Y ^ 2 := by
    simpa only [Even.pow_abs (by decide : Even 4)] using
      (step_fourth_le_sum Y v (by linarith)).trans (hfour v hvα hvβ)
  have hraw' := hraw.trans (mul_le_mul_of_nonneg_left hrate
    (show 0 ≤ 32 * (1 + A) * Y * (v ^ 2 * Real.log Y ^ 2) by positivity))
  have hcont : continuousPrimeMoment 4 Y v ≤ C * Y * v ^ 2 * Real.log Y ^ 2 := by
    have := (le_abs_self _).trans hraw'
    dsimp [C]
    nlinarith only [this, hstep]
  have hl := (band_log β Y v hβ (by linarith) hv hvβ).2.1
  have hlogs : Real.log Y ^ 2 ≤ Real.log (Y / v) ^ 2 / (1 - β) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hβ))).mpr
    nlinarith only [pow_le_pow_left₀ (mul_nonneg (sub_pos.mpr hβ).le hL) hl 2]
  change (∫ x in (1 : ℝ)..Y, |primeIncrement v x| ^ 4) ≤ _
  simp only [Even.pow_abs (by decide : Even 4)]
  calc
    continuousPrimeMoment 4 Y v ≤ C * Y * v ^ 2 * Real.log Y ^ 2 := hcont
    _ ≤ C * Y * v ^ 2 * (Real.log (Y / v) ^ 2 / (1 - β) ^ 2) := by gcongr
    _ = _ := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
