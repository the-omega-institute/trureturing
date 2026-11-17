/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthVariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Single-length prime moments give uniform cumulative variance asymptotics. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthRates
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthMoments
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthFourth

/-! The second-moment part of the single-length prime-moment transfer. -/

open Set Filter
open scoped Topology

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
open VarianceTransferDefs
noncomputable section
set_option autoImplicit false

private theorem discrete_second_error_uniform (α β : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4)
    (hMS : MSThirdTheorem) (hHL : HL4 concreteSS β) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      |discretePrimeMoment 2 ⌊Y⌋₊ ⌊v⌋₊ - montgomerySoundararajanMainTerm 2 Y v| ≤
        η * Y * v * Real.log (Y / v) := by
  obtain ⟨ε, hε, hεβ⟩ := transfer_epsilon_exists β hβ
  have hcorrelation : MS20 2 (polynomialLengthFamily β 2) :=
    hl4_implies_ms20 β 2 2 (by norm_num) (by norm_num) hHL
  obtain ⟨C, hC, hdisc⟩ := hMS 2 (Or.inl rfl) (polynomialLengthFamily β 2)
    hcorrelation ε hε
  have hδ : 0 < η / (2 * C) := by positivity
  filter_upwards [(tendsto_nat_floor_atTop (α := ℝ)).eventually hdisc,
    band_geometry α β hα hαβ hβ,
    ms_error_uniform 2 α β ε (η / (2 * C)) (Or.inl rfl) hα hαβ hβ hε hεβ hδ,
    main_errors_uniform 2 α β (η / 2) (Or.inl rfl) hα hαβ hβ (half_pos hη)]
    with Y hdisc hgeom herr hmain v hvα hvβ
  obtain ⟨hN, _, _, _, _, _, hfamily, hlog, hquarter⟩ := hgeom v hvα hvβ
  have hN1 : (1 : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast (by omega : 1 ≤ ⌊Y⌋₊)
  have hhalf : (⌊v⌋₊ : ℝ) ≤ (⌊Y⌋₊ : ℝ) ^ (1 / (2 : ℝ)) :=
    hquarter.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))
  have hd := hdisc ⌊v⌋₊ hfamily hlog hhalf
  have he : montgomerySoundararajanError 2 ε (⌊Y⌋₊ : ℝ) (⌊v⌋₊ : ℝ) ≤
      η / (2 * C) * Y * v * Real.log (Y / v) := by
    simpa only [Nat.reduceDiv, pow_one] using herr v hvα hvβ
  have hm : |montgomerySoundararajanMainTerm 2 (⌊Y⌋₊ : ℝ) (⌊v⌋₊ : ℝ) - montgomerySoundararajanMainTerm 2 Y v| ≤
      (η / 2) * Y * v * Real.log (Y / v) := by
    simpa only [Nat.reduceDiv, pow_one] using hmain v hvα hvβ
  have hscale := mul_le_mul_of_nonneg_left he hC.le
  have hid : C * (η / (2 * C) * Y * v * Real.log (Y / v)) =
      (η / 2) * Y * v * Real.log (Y / v) := by
    field_simp
  rw [hid] at hscale
  calc
    _ ≤ |discretePrimeMoment 2 ⌊Y⌋₊ ⌊v⌋₊ -
          montgomerySoundararajanMainTerm 2 (⌊Y⌋₊ : ℝ) (⌊v⌋₊ : ℝ)| +
        |montgomerySoundararajanMainTerm 2 (⌊Y⌋₊ : ℝ) (⌊v⌋₊ : ℝ) - montgomerySoundararajanMainTerm 2 Y v| := abs_sub_le _ _ _
    _ ≤ _ := by linarith only [hd, hscale, hm]

private theorem sampling_second_error_uniform (α β A : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4) (hA : 1 ≤ A)
    (hfourth : ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ A * Y * v ^ 2 * Real.log Y ^ 2)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      |continuousPrimeMoment 2 Y v - discretePrimeMoment 2 ⌊Y⌋₊ ⌊v⌋₊| ≤
        η * Y * v * Real.log (Y / v) := by
  obtain ⟨C, hC, hsample⟩ := sampling_second
  have hβ1 : β < 1 := hβ.trans (by norm_num)
  let δ := η * (1 - β) / (C * (1 + A))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  filter_upwards [hfourth,
    sampling_uniform 2 α β δ (Or.inl rfl) hα hαβ hβ hδ,
    eventually_ge_atTop (2 : ℝ)] with Y hfourth hrate hY v hvα hvβ
  have hY1 : 1 ≤ Y := by linarith only [hY]
  obtain ⟨hv1, hvY⟩ := FourthTransfer.FourthMomentAsymptotic.band_lengths
    hY1 hα hαβ hβ1 hvα hvβ
  have hY0 : 0 < Y := by positivity
  have hv0 : 0 < v := zero_lt_one.trans_le hv1
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY1
  have hraw := hsample A Y v hA hY hv1 hvY (hfourth v hvα hvβ)
  have hr : Real.sqrt (Real.log Y / v) + Real.log Y / v +
      (v * Real.log Y) / Y ≤ δ := by
    simpa only [cumulativeSamplingRate, Nat.cast_ofNat,
      show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one] using hrate v hvα hvβ
  have hscale := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ C * (1 + A) * Y * (v * Real.log Y) by positivity)
  have hid : C * (1 + A) * Y * (v * Real.log Y) * δ =
      η * Y * v * ((1 - β) * Real.log Y) := by
    dsimp only [δ]
    field_simp
  rw [hid] at hscale
  have hlower := (band_log β Y v hβ1 (by linarith only [hY]) hv1 hvβ).2.1
  exact hraw.trans (hscale.trans
    (mul_le_mul_of_nonneg_left hlower (by positivity)))

private theorem variance_asymptotic_of_discrete_fourth_bound (α β A : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4)
    (hMS : MSThirdTheorem) (hHL : HL4 concreteSS β) (hA : 1 ≤ A)
    (hfourth : ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ A * Y * v ^ 2 * Real.log Y ^ 2) :
    CumulativeVarianceBandAsymptoticFor chebyshevError α β := by
  intro η hη
  have hquarter : 0 < η / 4 := by positivity
  have hβ1 : β < 1 := hβ.trans (by norm_num)
  filter_upwards [sampling_second_error_uniform α β A hα hαβ hβ hA hfourth
      (η / 4) hquarter,
    discrete_second_error_uniform α β hα hαβ hβ hMS hHL (η / 4) hquarter,
    second_main_uniform α β hα hαβ hβ1 (η / 2) (half_pos hη),
    eventually_ge_atTop (2 : ℝ)] with Y hsample hdisc hmain hY v hvα hvβ
  have hY1 : 1 ≤ Y := by linarith only [hY]
  obtain ⟨hv1, _⟩ := FourthTransfer.FourthMomentAsymptotic.band_lengths
    hY1 hα hαβ hβ1 hvα hvβ
  have hlog := (band_log β Y v hβ1 (by linarith only [hY]) hv1 hvβ).1
  have hQ : 0 < Y * v * Real.log (Y / v) := by positivity
  have hs := hsample v hvα hvβ
  have hd := hdisc v hvα hvβ
  have hm := hmain v hvα hvβ
  have herr : |continuousPrimeMoment 2 Y v - montgomerySoundararajanMainTerm 2 Y v| ≤
      (η / 2) * (Y * v * Real.log (Y / v)) := by
    calc
      _ ≤ |continuousPrimeMoment 2 Y v - discretePrimeMoment 2 ⌊Y⌋₊ ⌊v⌋₊| +
          |discretePrimeMoment 2 ⌊Y⌋₊ ⌊v⌋₊ - montgomerySoundararajanMainTerm 2 Y v| := abs_sub_le _ _ _
      _ ≤ _ := by linarith only [hs, hd]
  have hnorm : |continuousPrimeMoment 2 Y v / (Y * v * Real.log (Y / v)) -
      montgomerySoundararajanMainTerm 2 Y v / (Y * v * Real.log (Y / v))| ≤ η / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hQ]
    exact (div_le_iff₀ hQ).mpr herr
  change |continuousPrimeMoment 2 Y v / (Y * v * Real.log (Y / v)) - 1| ≤ η
  calc
    _ ≤ |continuousPrimeMoment 2 Y v / (Y * v * Real.log (Y / v)) -
          montgomerySoundararajanMainTerm 2 Y v / (Y * v * Real.log (Y / v))| +
        |montgomerySoundararajanMainTerm 2 Y v / (Y * v * Real.log (Y / v)) - 1| := abs_sub_le _ _ _
    _ ≤ η := by linarith only [hnorm, hm]

/-- The Montgomery–Soundararajan formula and strong Hardy–Littlewood errors give
the uniform cumulative variance asymptotic for the complete Chebyshev error. -/
theorem ms_implies_490_2 (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4)
    (hMS : MSThirdTheorem) (hHL : HL4 concreteSS β) :
    CumulativeVarianceBandAsymptoticFor chebyshevError α β := by
  obtain ⟨A, hA, hfourth⟩ := discrete_fourth_upper α β hα hαβ hβ hMS hHL
  exact variance_asymptotic_of_discrete_fourth_bound α β A hα hαβ hβ hMS hHL hA hfourth

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
