/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic integrals control the single-length main terms. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SingleLengthMSDefs
import D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentAsymptotic

/-! Length and cutoff replacement estimates for the second and fourth scalar main terms. -/

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
open Set MeasureTheory
open D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentAsymptotic
noncomputable section
set_option autoImplicit false

theorem floor_log_difference (v : ℝ) (hv : 1 ≤ v) :
    |Real.log v - Real.log (⌊v⌋₊ : ℝ)| ≤ 1 / (⌊v⌋₊ : ℝ) := by
  have hK : (1 : ℝ) ≤ (⌊v⌋₊ : ℝ) := by
    have hnat : (1 : ℕ) ≤ ⌊v⌋₊ := Nat.le_floor (by simpa using hv)
    exact_mod_cast hnat
  have hK0 : 0 < (⌊v⌋₊ : ℝ) := by linarith
  have hv0 : 0 < v := by linarith
  have hKv := Nat.floor_le hv0.le
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hK0 hKv)),
    ← Real.log_div hv0.ne' hK0.ne']
  apply (Real.log_le_sub_one_of_pos (div_pos hv0 hK0)).trans
  apply (le_div_iff₀ hK0).2
  have hcancel : (v / (⌊v⌋₊ : ℝ) - 1) * (⌊v⌋₊ : ℝ) = v - (⌊v⌋₊ : ℝ) := by
    field_simp
  rw [hcancel]
  linarith [Nat.lt_floor_add_one v]

private lemma scalar_log_integral (Y v B : ℝ) (hY : 1 ≤ Y) (hv : 0 < v) :
    (∫ y in (1 : ℝ)..Y, Real.log (y / v) + B) =
      Y * Real.log (Y / v) + (B - 1) * Y + 1 + Real.log v - B := by
  have hfun : (∫ y in (1 : ℝ)..Y, Real.log (y / v) + B) =
      ∫ y in (1 : ℝ)..Y, Real.log y - Real.log v + B := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hY] at hy
    dsimp only
    rw [Real.log_div (ne_of_gt (zero_lt_one.trans_le hy.1)) hv.ne']
  rw [hfun, intervalIntegral.integral_add
    (intervalIntegral.intervalIntegrable_log'.sub intervalIntegrable_const)
    intervalIntegrable_const,
    intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_log'
      intervalIntegrable_const, integral_log]
  simp only [Real.log_one, mul_zero, intervalIntegral.integral_const, smul_eq_mul]
  rw [Real.log_div (ne_of_gt (zero_lt_one.trans_le hY)) hv.ne']
  ring

/-- The second main term has an exact elementary logarithmic expression. -/
theorem second_main_exact (Y v : ℝ) (hY : 1 ≤ Y) (hv : 0 < v) :
    montgomerySoundararajanMainTerm 2 Y v =
      v * (Y * Real.log (Y / v) + (montgomerySoundararajanConstant - 1) * Y + 1 + Real.log v - montgomerySoundararajanConstant) := by
  simpa only [montgomerySoundararajanMainTerm, ite_true, Nat.reduceDiv, pow_one, one_mul] using
    congrArg (v * ·) (scalar_log_integral Y v montgomerySoundararajanConstant hY hv)

private def logEnvelope : ℝ := 1 + (|montgomerySoundararajanConstant| + 1) / Real.log 2

private lemma log_envelope_bounds (Y : ℝ) (hY : 2 ≤ Y) :
    0 < logEnvelope ∧ 1 ≤ Real.log Y + |montgomerySoundararajanConstant| + 1 ∧
      Real.log Y + |montgomerySoundararajanConstant| + 1 ≤ logEnvelope * Real.log Y := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
  have hLY : 0 ≤ Real.log Y := h2.le.trans hL
  have hc : 0 ≤ (|montgomerySoundararajanConstant| + 1) / Real.log 2 := by positivity
  refine ⟨by unfold logEnvelope; positivity, by linarith [abs_nonneg montgomerySoundararajanConstant], ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hL hc
  have he : (|montgomerySoundararajanConstant| + 1) / Real.log 2 * Real.log 2 = |montgomerySoundararajanConstant| + 1 :=
    div_mul_cancel₀ _ h2.ne'
  rw [he] at hmul
  dsimp only [logEnvelope]
  nlinarith

private lemma weighted_floor_log_difference (v y B T : ℝ) (hv : 1 ≤ v)
    (hy : 0 < y) (hT : 1 ≤ T) (hbound : |Real.log (y / v) + B| ≤ T) :
    |(⌊v⌋₊ : ℝ) * (Real.log (y / (⌊v⌋₊ : ℝ)) + B) -
      v * (Real.log (y / v) + B)| ≤ 2 * T := by
  have hq : (1 : ℝ) ≤ (⌊v⌋₊ : ℝ) := by
    exact_mod_cast (Nat.le_floor (by simpa using hv) : (1 : ℕ) ≤ ⌊v⌋₊)
  have hq0 : 0 < (⌊v⌋₊ : ℝ) := zero_lt_one.trans_le hq
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hqv := Nat.floor_le hv0.le
  have hdiff : |(⌊v⌋₊ : ℝ) - v| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hqv)]
    linarith [Nat.lt_floor_add_one v]
  have hlog : (⌊v⌋₊ : ℝ) * |Real.log v - Real.log (⌊v⌋₊ : ℝ)| ≤ 1 := by
    calc
      _ ≤ (⌊v⌋₊ : ℝ) * (1 / (⌊v⌋₊ : ℝ)) :=
        mul_le_mul_of_nonneg_left (floor_log_difference v hv) hq0.le
      _ = 1 := mul_one_div_cancel hq0.ne'
  have he : (⌊v⌋₊ : ℝ) * (Real.log (y / (⌊v⌋₊ : ℝ)) + B) -
      v * (Real.log (y / v) + B) =
      ((⌊v⌋₊ : ℝ) - v) * (Real.log (y / v) + B) +
        (⌊v⌋₊ : ℝ) * (Real.log v - Real.log (⌊v⌋₊ : ℝ)) := by
    rw [Real.log_div hy.ne' hq0.ne', Real.log_div hy.ne' hv0.ne']
    ring
  rw [he]
  calc
    _ ≤ |((⌊v⌋₊ : ℝ) - v) * (Real.log (y / v) + B)| +
        |(⌊v⌋₊ : ℝ) * (Real.log v - Real.log (⌊v⌋₊ : ℝ))| := abs_add_le _ _
    _ = |(⌊v⌋₊ : ℝ) - v| * |Real.log (y / v) + B| +
        (⌊v⌋₊ : ℝ) * |Real.log v - Real.log (⌊v⌋₊ : ℝ)| := by
      rw [abs_mul, abs_mul, abs_of_pos hq0]
    _ ≤ 1 * T + 1 := add_le_add (mul_le_mul hdiff hbound (abs_nonneg _) zero_le_one) hlog
    _ ≤ 2 * T := by linarith

private lemma log_affine_integrable {a b v B : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hv : 0 < v) :
    IntervalIntegrable (fun y => Real.log (y / v) + B) volume a b := by
  apply IntervalIntegrable.add ?_ intervalIntegrable_const
  apply IntervalIntegrable.log (continuousOn_id.div_const v)
  intro y hy
  rw [uIcc_of_le hab] at hy
  exact (div_pos (ha.trans_le hy.1) hv).ne'

/-- Rounding the length changes the second main term by at most a constant times Y log Y. -/
theorem length_main_second :
    ∃ C : ℝ, 0 < C ∧ ∀ Y v : ℝ, 2 ≤ Y → 1 ≤ v → v ≤ Y →
      |montgomerySoundararajanMainTerm 2 Y (⌊v⌋₊ : ℝ) - montgomerySoundararajanMainTerm 2 Y v| ≤ C * Y * Real.log Y := by
  have hc : 0 < logEnvelope := (log_envelope_bounds 2 (by norm_num)).1
  refine ⟨2 * logEnvelope, by positivity, ?_⟩
  intro Y v hY hv hvY
  have hY1 : 1 ≤ Y := by linarith
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hq : (1 : ℝ) ≤ (⌊v⌋₊ : ℝ) := by
    exact_mod_cast (Nat.le_floor (by simpa using hv) : (1 : ℕ) ≤ ⌊v⌋₊)
  have hq0 : 0 < (⌊v⌋₊ : ℝ) := zero_lt_one.trans_le hq
  let T := Real.log Y + |montgomerySoundararajanConstant| + 1
  obtain ⟨_, hT1, hTc⟩ := log_envelope_bounds Y hY
  have hbound (y : ℝ) (hy : y ∈ Icc (1 : ℝ) Y) :
      |Real.log (y / v) + montgomerySoundararajanConstant| ≤ T := by
    calc
      _ ≤ |Real.log (y / v)| + |montgomerySoundararajanConstant| := abs_add_le _ _
      _ ≤ Real.log Y + |montgomerySoundararajanConstant| := add_le_add (log_ratio_abs_le hY1 hv hvY hy) le_rfl
      _ ≤ T := by dsimp only [T]; linarith
  have hiq := (log_affine_integrable zero_lt_one hY1 hq0 (B := montgomerySoundararajanConstant)).const_mul
    (⌊v⌋₊ : ℝ)
  have hiv := (log_affine_integrable zero_lt_one hY1 hv0 (B := montgomerySoundararajanConstant)).const_mul v
  have hInt : |∫ y in (1 : ℝ)..Y,
      (⌊v⌋₊ : ℝ) * (Real.log (y / (⌊v⌋₊ : ℝ)) + montgomerySoundararajanConstant) -
        v * (Real.log (y / v) + montgomerySoundararajanConstant)| ≤ (2 * T) * |Y - 1| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [Real.norm_eq_abs]
    rw [uIoc_of_le hY1] at hy
    exact weighted_floor_log_difference v y montgomerySoundararajanConstant T hv
      (zero_lt_one.trans hy.1) hT1 (hbound y ⟨hy.1.le, hy.2⟩)
  simp only [montgomerySoundararajanMainTerm, ite_true, Nat.reduceDiv, pow_one, one_mul]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub hiq hiv]
  calc
    _ ≤ (2 * T) * |Y - 1| := hInt
    _ ≤ (2 * T) * Y := by
      rw [abs_of_nonneg (sub_nonneg.mpr hY1)]
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ ≤ (2 * (logEnvelope * Real.log Y)) * Y := by gcongr
    _ = _ := by ring

/-- Rounding the length changes the fourth main term by at most C Y v log² Y. -/
theorem length_main_fourth :
    ∃ C : ℝ, 0 < C ∧ ∀ Y v : ℝ, 2 ≤ Y → 1 ≤ v → v ≤ Y →
      |montgomerySoundararajanMainTerm 4 Y (⌊v⌋₊ : ℝ) - montgomerySoundararajanMainTerm 4 Y v| ≤ C * Y * v * Real.log Y ^ 2 := by
  have hc : 0 < logEnvelope := (log_envelope_bounds 2 (by norm_num)).1
  refine ⟨12 * logEnvelope ^ 2, by positivity, ?_⟩
  intro Y v hY hv hvY
  have hY1 : 1 ≤ Y := by linarith
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hq : (1 : ℝ) ≤ (⌊v⌋₊ : ℝ) := by
    exact_mod_cast (Nat.le_floor (by simpa using hv) : (1 : ℕ) ≤ ⌊v⌋₊)
  have hq0 : 0 < (⌊v⌋₊ : ℝ) := zero_lt_one.trans_le hq
  have hqv := Nat.floor_le hv0.le
  let T := Real.log Y + |montgomerySoundararajanConstant| + 1
  obtain ⟨_, hT1, hTc⟩ := log_envelope_bounds Y hY
  have hT0 : 0 ≤ T := by dsimp only [T]; linarith
  have hpoint (y : ℝ) (hy : y ∈ Icc (1 : ℝ) Y) :
      |(⌊v⌋₊ : ℝ) ^ 2 * (Real.log (y / (⌊v⌋₊ : ℝ)) + montgomerySoundararajanConstant) ^ 2 -
        v ^ 2 * (Real.log (y / v) + montgomerySoundararajanConstant) ^ 2| ≤ 4 * v * T ^ 2 := by
    have hbound (u : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) :
        |Real.log (y / u) + montgomerySoundararajanConstant| ≤ T := by
      calc
        _ ≤ |Real.log (y / u)| + |montgomerySoundararajanConstant| := abs_add_le _ _
        _ ≤ Real.log Y + |montgomerySoundararajanConstant| :=
          add_le_add (log_ratio_abs_le hY1 hu (huv.trans hvY) hy) le_rfl
        _ ≤ T := by dsimp only [T]; linarith
    have hraw (u : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) :
        |u * (Real.log (y / u) + montgomerySoundararajanConstant)| ≤ v * T := by
      rw [abs_mul, abs_of_nonneg (zero_le_one.trans hu)]
      exact mul_le_mul huv (hbound u hu huv) (abs_nonneg _) hv0.le
    have hmax : max |(⌊v⌋₊ : ℝ) * (Real.log (y / (⌊v⌋₊ : ℝ)) + montgomerySoundararajanConstant)|
        |v * (Real.log (y / v) + montgomerySoundararajanConstant)| ≤ v * T :=
      max_le (hraw _ hq hqv) (hraw v hv le_rfl)
    have hd := weighted_floor_log_difference v y montgomerySoundararajanConstant T hv
      (zero_lt_one.trans_le hy.1) hT1 (hbound v hv le_rfl)
    have hp := abs_pow_sub_pow_le
      ((⌊v⌋₊ : ℝ) * (Real.log (y / (⌊v⌋₊ : ℝ)) + montgomerySoundararajanConstant))
      (v * (Real.log (y / v) + montgomerySoundararajanConstant)) 2
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hp
    rw [← mul_pow, ← mul_pow]
    calc
      _ ≤ |(⌊v⌋₊ : ℝ) * (Real.log (y / (⌊v⌋₊ : ℝ)) + montgomerySoundararajanConstant) -
          v * (Real.log (y / v) + montgomerySoundararajanConstant)| * 2 *
          max |(⌊v⌋₊ : ℝ) * (Real.log (y / (⌊v⌋₊ : ℝ)) + montgomerySoundararajanConstant)|
            |v * (Real.log (y / v) + montgomerySoundararajanConstant)| := hp
      _ ≤ (2 * T) * 2 * (v * T) := by gcongr
      _ = _ := by ring
  have hiq := (log_square_integrable zero_lt_one hY1 hq0 (B := montgomerySoundararajanConstant)).const_mul
    ((⌊v⌋₊ : ℝ) ^ 2)
  have hiv := (log_square_integrable zero_lt_one hY1 hv0 (B := montgomerySoundararajanConstant)).const_mul (v ^ 2)
  have hInt : |∫ y in (1 : ℝ)..Y,
      (⌊v⌋₊ : ℝ) ^ 2 * (Real.log (y / (⌊v⌋₊ : ℝ)) + montgomerySoundararajanConstant) ^ 2 -
        v ^ 2 * (Real.log (y / v) + montgomerySoundararajanConstant) ^ 2| ≤ (4 * v * T ^ 2) * |Y - 1| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [Real.norm_eq_abs, uIoc_of_le hY1] at *
    exact hpoint y ⟨hy.1.le, hy.2⟩
  have he : montgomerySoundararajanMainTerm 4 Y (⌊v⌋₊ : ℝ) - montgomerySoundararajanMainTerm 4 Y v =
      3 * (∫ y in (1 : ℝ)..Y,
        (⌊v⌋₊ : ℝ) ^ 2 * (Real.log (y / (⌊v⌋₊ : ℝ)) + montgomerySoundararajanConstant) ^ 2 -
          v ^ 2 * (Real.log (y / v) + montgomerySoundararajanConstant) ^ 2) := by
    rw [intervalIntegral.integral_sub hiq hiv,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    norm_num only [montgomerySoundararajanMainTerm, show ¬(4 : ℕ) = 2 by decide, ite_false, Nat.reduceDiv]
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  calc
    _ ≤ 3 * ((4 * v * T ^ 2) * |Y - 1|) := mul_le_mul_of_nonneg_left hInt (by norm_num)
    _ ≤ 3 * ((4 * v * T ^ 2) * Y) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hY1)]
      gcongr
      linarith
    _ ≤ 3 * ((4 * v * (logEnvelope * Real.log Y) ^ 2) * Y) := by gcongr
    _ = _ := by ring

private lemma cutoff_log_power (p : ℕ) (hp : p = 1 ∨ p = 2) (Y : ℝ) (K : ℕ)
    (hY : 2 ≤ Y) (hK : 1 ≤ K) (hKY : (K : ℝ) ≤ Y) :
    |(∫ y in (1 : ℝ)..Y, (Real.log (y / (K : ℝ)) + montgomerySoundararajanConstant) ^ p) -
      (∫ y in (1 : ℝ)..(⌊Y⌋₊ : ℝ), (Real.log (y / (K : ℝ)) + montgomerySoundararajanConstant) ^ p)| ≤
        (logEnvelope * Real.log Y) ^ p := by
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : 0 < (K : ℝ) := zero_lt_one.trans_le hK1
  have hN1 : (1 : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by
    exact_mod_cast (Nat.le_floor (by simpa using hY1) : (1 : ℕ) ≤ ⌊Y⌋₊)
  have hNY := Nat.floor_le hY0
  have hi (b : ℝ) (hb : 1 ≤ b) :
      IntervalIntegrable (fun y => (Real.log (y / (K : ℝ)) + montgomerySoundararajanConstant) ^ p) volume 1 b := by
    rcases hp with rfl | rfl
    · simpa only [pow_one] using (log_affine_integrable zero_lt_one hb hK0 (B := montgomerySoundararajanConstant))
    · exact log_square_integrable zero_lt_one hb hK0
  rw [intervalIntegral.integral_interval_sub_left (hi Y hY1) (hi _ hN1)]
  have hInt : ‖∫ y in (⌊Y⌋₊ : ℝ)..Y,
      (Real.log (y / (K : ℝ)) + montgomerySoundararajanConstant) ^ p‖ ≤
        (logEnvelope * Real.log Y) ^ p * |Y - (⌊Y⌋₊ : ℝ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [uIoc_of_le hNY] at hy
    have hycc : y ∈ Icc (1 : ℝ) Y := ⟨hN1.trans hy.1.le, hy.2⟩
    have hbound : |Real.log (y / (K : ℝ)) + montgomerySoundararajanConstant| ≤ logEnvelope * Real.log Y := by
      calc
        _ ≤ |Real.log (y / (K : ℝ))| + |montgomerySoundararajanConstant| := abs_add_le _ _
        _ ≤ Real.log Y + |montgomerySoundararajanConstant| :=
          add_le_add (log_ratio_abs_le hY1 hK1 hKY hycc) le_rfl
        _ ≤ Real.log Y + |montgomerySoundararajanConstant| + 1 := by linarith
        _ ≤ _ := (log_envelope_bounds Y hY).2.2
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hbound p
  rw [Real.norm_eq_abs] at hInt
  have hwidth : |Y - (⌊Y⌋₊ : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hNY)]
    linarith [Nat.lt_floor_add_one Y]
  have hC : 0 ≤ (logEnvelope * Real.log Y) ^ p := by
    have hc := (log_envelope_bounds Y hY).1
    have hL := Real.log_nonneg hY1
    positivity
  exact hInt.trans ((mul_le_mul_of_nonneg_left hwidth hC).trans_eq (mul_one _))

/-- Rounding the cutoff changes either main term by one logarithmic integrand bound. -/
theorem cutoff_main_term (k : ℕ) (hk : k = 2 ∨ k = 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℝ) (K : ℕ), 2 ≤ Y → 1 ≤ K → (K : ℝ) ≤ Y →
      |montgomerySoundararajanMainTerm k Y (K : ℝ) - montgomerySoundararajanMainTerm k (⌊Y⌋₊ : ℝ) (K : ℝ)| ≤
        C * (K : ℝ) ^ (k / 2) * Real.log Y ^ (k / 2) := by
  have hc : 0 < logEnvelope := (log_envelope_bounds 2 (by norm_num)).1
  rcases hk with rfl | rfl
  · refine ⟨logEnvelope, hc, ?_⟩
    intro Y K hY hK hKY
    have hi := cutoff_log_power 1 (Or.inl rfl) Y K hY hK hKY
    simp only [pow_one] at hi
    simp only [montgomerySoundararajanMainTerm, ite_true, Nat.reduceDiv, pow_one, one_mul]
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg K)]
    calc
      _ ≤ (K : ℝ) * (logEnvelope * Real.log Y) :=
        mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg K)
      _ = _ := by ring
  · refine ⟨3 * logEnvelope ^ 2, by positivity, ?_⟩
    intro Y K hY hK hKY
    have hi := cutoff_log_power 2 (Or.inr rfl) Y K hY hK hKY
    norm_num only [montgomerySoundararajanMainTerm, show ¬(4 : ℕ) = 2 by decide, ite_false, Nat.reduceDiv]
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 * (K : ℝ) ^ 2)]
    calc
      _ ≤ (3 * (K : ℝ) ^ 2) * (logEnvelope * Real.log Y) ^ 2 :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
