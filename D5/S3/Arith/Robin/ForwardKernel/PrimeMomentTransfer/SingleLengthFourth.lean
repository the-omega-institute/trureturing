/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthFourth
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthFourth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The single-length moment formula yields uniform cumulative fourth moments. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthRates
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthMoments

/-! Uniform discrete bounds and the fourth-moment part of Corollary 498.5. -/

open Set Filter MeasureTheory
open scoped Topology

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
open FourthTransfer.FourthMomentAsymptotic
noncomputable section
set_option autoImplicit false

private theorem main_fourth_upper (Y v : ℝ) (hY : 1 ≤ Y) (hlog : 1 ≤ Real.log Y)
    (hv : 1 ≤ v) (hvY : v ≤ Y) :
    montgomerySoundararajanMainTerm 4 Y v ≤ 3 * (1 + |montgomerySoundararajanConstant|) ^ 2 * Y * v ^ 2 * Real.log Y ^ 2 := by
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hbound (y : ℝ) (hy : y ∈ Icc (1 : ℝ) Y) :
      |Real.log (y / v) + montgomerySoundararajanConstant| ≤ (1 + |montgomerySoundararajanConstant|) * Real.log Y := by
    calc
      _ ≤ |Real.log (y / v)| + |montgomerySoundararajanConstant| := abs_add_le _ _
      _ ≤ Real.log Y + |montgomerySoundararajanConstant| := add_le_add (log_ratio_abs_le hY hv hvY hy) le_rfl
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left hlog (abs_nonneg montgomerySoundararajanConstant)
        linarith only [hm]
  have hi := log_square_integral_le zero_lt_one hY hv0
    (show 0 ≤ (1 + |montgomerySoundararajanConstant|) * Real.log Y by positivity) hbound
  have hi' := hi.trans (mul_le_mul_of_nonneg_right
    (show Y - 1 ≤ Y by linarith) (sq_nonneg _))
  simp only [montgomerySoundararajanMainTerm, show ¬ (4 : ℕ) = 2 by decide, ite_false, Nat.reduceDiv]
  calc
    _ ≤ 3 * v ^ 2 * (Y * ((1 + |montgomerySoundararajanConstant|) * Real.log Y) ^ 2) :=
      mul_le_mul_of_nonneg_left hi' (by positivity)
    _ = _ := by ring

private theorem discrete_fourth_approximation (α β η : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4)
    (hMS : MSThirdTheorem) (hHL : HL4 concreteSS β) (hη : 0 < η) :
    ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ, Y ^ α ≤ v → v ≤ Y ^ β →
      |discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ - montgomerySoundararajanMainTerm 4 Y v| ≤
        η * Y * v ^ 2 * Real.log (Y / v) ^ 2 := by
  obtain ⟨ε, hε, hεβ⟩ := transfer_epsilon_exists β hβ
  have hcorrelation : MS20 4 (polynomialLengthFamily β 2) :=
    hl4_implies_ms20 β 2 4 (by norm_num) le_rfl hHL
  obtain ⟨C, hC, hms⟩ := hMS 4 (Or.inr rfl) (polynomialLengthFamily β 2)
    hcorrelation ε hε
  have hmsR := (tendsto_nat_floor_atTop (α := ℝ)).eventually hms
  filter_upwards [hmsR, band_geometry α β hα hαβ hβ,
    ms_error_uniform 4 α β ε (η / (2 * C)) (Or.inr rfl)
      hα hαβ hβ hε hεβ (by positivity),
    main_errors_uniform 4 α β (η / 2) (Or.inr rfl) hα hαβ hβ (by positivity)]
    with Y hmsY hgeom herr hmain v hvα hvβ
  obtain ⟨_, _, _, _, _, _, hfamily, hlog, hquarter⟩ := hgeom v hvα hvβ
  have h₁ := hmsY ⌊v⌋₊ hfamily hlog hquarter
  have h₂ := mul_le_mul_of_nonneg_left (herr v hvα hvβ) hC.le
  have hid : C * (η / (2 * C) * Y * v ^ 2 * Real.log (Y / v) ^ 2) =
      (η / 2) * Y * v ^ 2 * Real.log (Y / v) ^ 2 := by
    field_simp
  norm_num only [Nat.reduceDiv] at h₂
  rw [hid] at h₂
  have h₃ := hmain v hvα hvβ
  norm_num only [Nat.reduceDiv] at h₃
  calc
    _ ≤ |discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ -
        montgomerySoundararajanMainTerm 4 (⌊Y⌋₊ : ℝ) (⌊v⌋₊ : ℝ)| +
        |montgomerySoundararajanMainTerm 4 (⌊Y⌋₊ : ℝ) (⌊v⌋₊ : ℝ) - montgomerySoundararajanMainTerm 4 Y v| := abs_sub_le _ _ _
    _ ≤ (η / 2) * Y * v ^ 2 * Real.log (Y / v) ^ 2 +
        (η / 2) * Y * v ^ 2 * Real.log (Y / v) ^ 2 := add_le_add (h₁.trans h₂) h₃
    _ = _ := by ring

/-- The integer fourth moment is uniformly bounded before continuous sampling. -/
theorem discrete_fourth_upper (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hβ : β < 1 / 4) (hMS : MSThirdTheorem) (hHL : HL4 concreteSS β) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ Y : ℝ in atTop, ∀ v : ℝ,
      Y ^ α ≤ v → v ≤ Y ^ β →
        discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ ≤ A * Y * v ^ 2 * Real.log Y ^ 2 := by
  refine ⟨3 * (1 + |montgomerySoundararajanConstant|) ^ 2 + 1, by linarith only [sq_nonneg (1 + |montgomerySoundararajanConstant|)], ?_⟩
  filter_upwards [discrete_fourth_approximation α β 1 hα hαβ hβ hMS hHL zero_lt_one,
    eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with Y happ hY hlog v hvα hvβ
  have hβ1 : β < 1 := hβ.trans (by norm_num)
  have hY1 : 1 ≤ Y := by linarith only [hY]
  obtain ⟨hv, hvY⟩ := band_lengths hY1 hα hαβ hβ1 hvα hvβ
  obtain ⟨hL, _, hLhi⟩ := band_log β Y v hβ1 (by linarith only [hY]) hv hvβ
  have hnorm : Y * v ^ 2 * Real.log (Y / v) ^ 2 ≤
      Y * v ^ 2 * Real.log Y ^ 2 := by
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le hLhi 2) (by positivity)
  have he := ((abs_le.mp (happ v hvα hvβ)).2).trans (by simpa using hnorm)
  have hm := main_fourth_upper Y v hY1 hlog hv hvY
  calc
    _ ≤ montgomerySoundararajanMainTerm 4 Y v + Y * v ^ 2 * Real.log Y ^ 2 := by linarith only [he]
    _ ≤ 3 * (1 + |montgomerySoundararajanConstant|) ^ 2 * Y * v ^ 2 * Real.log Y ^ 2 +
        Y * v ^ 2 * Real.log Y ^ 2 := add_le_add hm le_rfl
    _ = _ := by ring

/-- Corollary 498.5: the uniform cumulative fourth moment follows from Theorem 3 and HL4. -/
theorem ms_implies_497_6 (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 4)
    (hMS : MSThirdTheorem) (hHL : HL4 concreteSS β) :
    FourthMomentAsymptoticFor chebyshevError α β montgomerySoundararajanConstant := by
  intro η hη
  obtain ⟨A, hA, hdisc⟩ := discrete_fourth_upper α β hα hαβ hβ hMS hHL
  obtain ⟨C, hC, hsample⟩ := sampling_fourth
  let δ := η * (1 - β) ^ 2 / (3 * C * (1 + A))
  have hβ1 : β < 1 := hβ.trans (by norm_num)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  filter_upwards [hdisc,
    discrete_fourth_approximation α β (2 * η / 3) hα hαβ hβ hMS hHL (by positivity),
    sampling_uniform 4 α β δ (Or.inr rfl) hα hαβ hβ hδ,
    eventually_ge_atTop (2 : ℝ)] with Y hdisc happ hsmall hY v hvα hvβ
  have hY1 : 1 ≤ Y := by linarith only [hY]
  obtain ⟨hv, hvY⟩ := band_lengths hY1 hα hαβ hβ1 hvα hvβ
  have hlog : 0 ≤ Real.log Y := Real.log_nonneg hY1
  obtain ⟨_, hlower, _⟩ := band_log β Y v hβ1 (by linarith only [hY]) hv hvβ
  have hs : Real.sqrt (Real.log Y / v) + (Real.log Y / v) ^ 2 +
      (v * Real.log Y) ^ 2 / Y ≤ δ := by
    simpa only [cumulativeSamplingRate, Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num,
      Real.rpow_two] using hsmall v hvα hvβ
  have hscaled := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ C * (1 + A) * Y * (v * Real.log Y) ^ 2 by positivity)
  have hid : C * (1 + A) * Y * (v * Real.log Y) ^ 2 * δ =
      (η / 3) * Y * v ^ 2 * ((1 - β) * Real.log Y) ^ 2 := by
    dsimp only [δ]
    field_simp
  rw [hid] at hscaled
  have hnorm := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (show 0 ≤ (1 - β) * Real.log Y by positivity) hlower 2)
    (show 0 ≤ (η / 3) * Y * v ^ 2 by positivity)
  have hsamp : |continuousPrimeMoment 4 Y v - discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊| ≤
      (η / 3) * Y * v ^ 2 * Real.log (Y / v) ^ 2 :=
    (hsample A Y v hA hY hv hvY (hdisc v hvα hvβ)).trans (hscaled.trans hnorm)
  have hresult : |continuousPrimeMoment 4 Y v - montgomerySoundararajanMainTerm 4 Y v| ≤
      η * Y * v ^ 2 * Real.log (Y / v) ^ 2 := by
    calc
      _ ≤ |continuousPrimeMoment 4 Y v - discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊| +
          |discretePrimeMoment 4 ⌊Y⌋₊ ⌊v⌋₊ - montgomerySoundararajanMainTerm 4 Y v| := abs_sub_le _ _ _
      _ ≤ (η / 3) * Y * v ^ 2 * Real.log (Y / v) ^ 2 +
          (2 * η / 3) * Y * v ^ 2 * Real.log (Y / v) ^ 2 :=
        add_le_add hsamp (happ v hvα hvβ)
      _ = _ := by ring
  simpa only [continuousPrimeMoment, montgomerySoundararajanMainTerm, primeIncrement, Nat.reduceDiv,
    show ¬ (4 : ℕ) = 2 by decide, ite_false, Even.pow_abs (by decide : Even (4 : ℕ))]
    using hresult

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
