/- GID: D5/S3/Weil/PrimeNumberTheorem/Smooth1
   generality: G
   mirror-B: D5/B/S3/Weil/PrimeNumberTheorem/Smooth1
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mellin convolution gives smooth threshold functions and their analytic bounds. -/

/-
Source: AlexKontorovich/PrimeNumberTheoremAnd, revision 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01.
Original file: PrimeNumberTheoremAnd/MellinCalculus.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0.
Full license and upstream attribution: Library/Weil/primenumbertheoremand2026medium.md.
This file is modified from the cited source.
Retirement: replace this consumed closure with direct references when this
repository's adopted Mathlib revision contains equivalent quantified contracts.
-/

import D5.S3.Weil.PrimeNumberTheorem.MellinCalculus

set_option lang.lemmaCmd true

open scoped ContDiff
open Complex Topology Filter Real MeasureTheory Set

local notation (name := mellintransform) "𝓜" => mellin

noncomputable def Smooth1 (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) (DeltaSpike ν ε)

lemma Smooth1Properties_below {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ (c : ℝ), 0 < c ∧ c = Real.log 2 ∧
      ∀ (ε x) (_ : 0 < ε), 0 < x → x ≤ 1 - c * ε → Smooth1 ν ε x = 1 := by
  have hSym {𝕂 : Type} [RCLike 𝕂] (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
      MellinConvolution f g x = MellinConvolution g f x := by
    have hMul (h : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
        ∫ y in Ioi 0, h (y * a) / y = ∫ y in Ioi 0, h y / y := by
      have hh := integral_comp_mul_right_Ioi (fun y ↦ h y / y) 0 ha
      simp only [RCLike.ofReal_mul, zero_mul, eq_inv_smul_iff₀ (ne_of_gt ha)] at hh
      rw [← integral_smul] at hh
      rw [← hh, setIntegral_congr_fun (by simp)]
      intro _ _
      simp only [RCLike.real_smul_eq_coe_mul]
      rw [mul_comm (a : 𝕂), div_mul, mul_div_assoc, div_self ?_, mul_one]
      exact (RCLike.ofReal_ne_zero).mpr <| ne_of_gt ha
    have hInv (h : ℝ → 𝕂) :
        ∫ y in Ioi 0, h (1 / y) / y = ∫ y in Ioi 0, h y / y := by
      have hh := integral_comp_rpow_Ioi (fun y ↦ h y / y) (p := -1) (by simp)
      rw [← hh, setIntegral_congr_fun (by simp)]
      intro y hy
      have : (y : 𝕂) ≠ 0 := (RCLike.ofReal_ne_zero).mpr <| LT.lt.ne' hy
      simp only [abs_neg, abs_one, rpow_neg_one, map_inv₀, div_inv_eq_mul,
        RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]
      ring_nf
      simp [field]
    unfold MellinConvolution
    calc
      _ = ∫ y in Ioi 0, f (y * x) * g (1 / y) / y := ?_
      _ = _ := ?_
    · rw [← hMul (fun y ↦ f y * g (x / y)) xpos]
      simp [div_mul_cancel_right₀ <| ne_of_gt xpos]
    · convert (hInv fun y ↦ f (y * x) * g (1 / y)).symm using 3
      rw [one_div_one_div, mul_comm, mul_comm_div, one_mul]
  have DeltaSpikeSupport_aux {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
      (suppν : ν.support ⊆ Icc (1 / 2) 2) :
      (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x).support ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
    unfold DeltaSpike
    simp only [one_div, Function.support_subset_iff, ne_eq, ite_eq_left_iff, not_lt, div_eq_zero_iff,
      not_forall, exists_prop, mem_Icc, and_imp]
    intro x hx h; push Not at h
    have := suppν <| Function.mem_support.mpr h.1
    simp only [one_div, mem_Icc] at this
    have hl := (le_rpow_inv_iff_of_pos (by norm_num) hx εpos).mp this.1
    rw [inv_rpow (by norm_num) ε, ← rpow_neg (by norm_num)] at hl
    refine ⟨hl, (rpow_inv_le_iff_of_pos ?_ (by norm_num) εpos).mp this.2⟩
    linarith [(by apply rpow_nonneg (by norm_num) : 0 ≤ (2 : ℝ) ^ (-ε))]
  have Smooth1Properties_estimate {ε : ℝ} (εpos : 0 < ε) :
      (1 - 2 ^ (-ε)) / ε < Real.log 2 := by
    apply (div_lt_iff₀' εpos).mpr
    have : 1 - 1 / (2 : ℝ) ^ ε = ((2 : ℝ) ^ ε - 1) / (2 : ℝ) ^ ε := by
      rw [sub_div, div_self (by positivity)]
    rw [← Real.log_rpow (by norm_num), rpow_neg (by norm_num), inv_eq_one_div (2 ^ ε), this]
    set c := (2 : ℝ) ^ ε
    have hc : 1 < c := by
      rw [← rpow_zero (2 : ℝ)]
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) εpos
    apply (div_lt_iff₀' (by positivity)).mpr <| lt_sub_iff_add_lt'.mp ?_
    let f := (fun x ↦ x * Real.log x - x)
    rw [(by simp [f] : -1 = f 1), (by simp [f] : c * Real.log c - c = f c)]
    have mono: StrictMonoOn f <| Ici 1 := by
      refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
      · apply continuousOn_id.mul (continuousOn_id.log ?_) |>.sub continuousOn_id
        intro x hx; simp only [mem_Ici] at hx; simp only [id_eq, ne_eq]; linarith
      · intro x hx; simp only [nonempty_Iio, interior_Ici', mem_Ioi] at hx
        dsimp only [f]
        rw [deriv_fun_sub, deriv_fun_mul, Real.deriv_log, deriv_id'', one_mul, mul_inv_cancel₀]
        · simp [log_pos hx]
        · linarith
        · simp only [differentiableAt_fun_id]
        · simp only [differentiableAt_log_iff, ne_eq]; linarith
        · exact differentiableAt_fun_id.mul <| differentiableAt_fun_id.log (by linarith)
        · simp only [differentiableAt_fun_id]
    exact mono (by rw [mem_Ici]) (mem_Ici.mpr <| le_of_lt hc) hc
  have deltaSpikeSupport {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
      (suppν : ν.support ⊆ Icc (1 / 2) 2) :
      DeltaSpike ν ε x ≠ 0 → x ∈ Icc (2 ^ (-ε)) (2 ^ ε) := by
    intro h
    have heq : (fun z ↦ if z < 0 then 0 else DeltaSpike ν ε z) x =
        DeltaSpike ν ε x := by simp [xnonneg]
    rw [← heq] at h
    exact (Function.support_subset_iff.mp <| DeltaSpikeSupport_aux εpos suppν) _ h
  have hDiv (h : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
      ∫ y in Ioi 0, h (a / y) / y = ∫ y in Ioi 0, h y / y := by
    simpa only [MellinConvolution, one_mul, mul_one, RCLike.ofReal_real_eq_id, id_eq] using
      (hSym (𝕂 := ℝ) (fun _ : ℝ ↦ (1 : ℝ)) h ha)
  set c := Real.log 2; use c
  refine ⟨log_pos (by norm_num), rfl, ?_⟩
  intro ε x εpos xpos hx
  have hx2 : x < 2 ^ (-ε) := by
    calc
      x ≤ 1 - Real.log 2 * ε := hx
      _ < 2 ^ (-ε) := ?_
    rw [sub_lt_iff_lt_add, add_comm, ← sub_lt_iff_lt_add]
    exact (div_lt_iff₀ εpos).mp <| Smooth1Properties_estimate εpos
  have deltaSpikeMass : ∫ y in Ioi 0, DeltaSpike ν ε y / y = 1 := by
    calc
      _ = ∫ (y : ℝ) in Ioi 0, (|1 / ε| * y ^ (1 / ε - 1)) •
          ((fun z ↦ ν z / z) (y ^ (1 / ε))) := by
        apply setIntegral_congr_ae measurableSet_Ioi
        filter_upwards with y hy
        simp only [smul_eq_mul, abs_of_pos (one_div_pos.mpr εpos)]
        symm; calc
          _ = (ν (y ^ (1 / ε)) / y ^ (1 / ε)) * y ^ (1 / ε - 1) * (1 / ε) := by ring
          _ = _ := by rw [rpow_sub hy, rpow_one]
          _ = (ν (y ^ (1 / ε)) / y ^ (1 / ε) * y ^ (1 / ε) / y) * (1 / ε) := by ring
          _ = _ := by rw [div_mul_cancel₀ _ (ne_of_gt (rpow_pos_of_pos hy (1 / ε)))]
          _ = ν (y ^ (1 / ε)) / ε / y := by ring
      _ = 1 := by
        rw [integral_comp_rpow_Ioi (fun z ↦ ν z / z), ← mass_one]
        simp only [ne_eq, div_eq_zero_iff, one_ne_zero, εpos.ne', or_self, not_false_eq_true]
  rewrite [← deltaSpikeMass]
  unfold Smooth1 MellinConvolution
  calc
    _ = ∫ (y : ℝ) in Ioi 0,
        indicator (Ioc 0 1) (fun y ↦ DeltaSpike ν ε (x / y) / ↑y) y := ?_
    _ = ∫ (y : ℝ) in Ioi 0, DeltaSpike ν ε (x / y) / y := ?_
    _ = _ := hDiv (fun y ↦ DeltaSpike ν ε y) xpos
  · rw [setIntegral_congr_fun (by simp)]
    intro y hy
    by_cases h : y ≤ 1 <;> simp [indicator, mem_Ioi.mp hy, h]
  · rw [setIntegral_congr_fun (by simp)]
    intro y hy
    have : y ≠ 0 := by
      rintro rfl
      simp at hy
    simp only [indicator_apply_eq_self, mem_Ioc, not_and, not_le, div_eq_zero_iff, this, or_false]
    intro hy2; replace hy2 := hy2 <| mem_Ioi.mp hy
    have hOutside : x / y ∉ Icc (2 ^ (-ε)) (2 ^ ε) := by
      simp only [mem_Icc, not_and, not_le]
      intro hMem
      have hLT : x / y < 2 ^ (-ε) := by
        apply (div_lt_iff₀ (by linarith)).mpr
        nlinarith
      linarith [hMem]
    have hNonneg : 0 ≤ x / y := by
      rw [le_div_iff₀ (by linarith), zero_mul]
      exact xpos.le
    by_contra hNZ
    exact hOutside (deltaSpikeSupport εpos hNonneg suppν hNZ)



lemma Smooth1Properties_above {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ (c : ℝ), 0 < c ∧ c = 2 * Real.log 2 ∧
      ∀ (ε x) (_ : ε ∈ Ioo 0 1), 1 + c * ε ≤ x → Smooth1 ν ε x = 0 := by
  have DeltaSpikeSupport_aux {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
      (suppν : ν.support ⊆ Icc (1 / 2) 2) :
      (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x).support ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
    unfold DeltaSpike
    simp only [one_div, Function.support_subset_iff, ne_eq, ite_eq_left_iff, not_lt, div_eq_zero_iff,
      not_forall, exists_prop, mem_Icc, and_imp]
    intro x hx h; push Not at h
    have := suppν <| Function.mem_support.mpr h.1
    simp only [one_div, mem_Icc] at this
    have hl := (le_rpow_inv_iff_of_pos (by norm_num) hx εpos).mp this.1
    rw [inv_rpow (by norm_num) ε, ← rpow_neg (by norm_num)] at hl
    refine ⟨hl, (rpow_inv_le_iff_of_pos ?_ (by norm_num) εpos).mp this.2⟩
    linarith [(by apply rpow_nonneg (by norm_num) : 0 ≤ (2 : ℝ) ^ (-ε))]
  have Smooth1Properties_estimate {ε : ℝ} (εpos : 0 < ε) :
      (1 - 2 ^ (-ε)) / ε < Real.log 2 := by
    apply (div_lt_iff₀' εpos).mpr
    have : 1 - 1 / (2 : ℝ) ^ ε = ((2 : ℝ) ^ ε - 1) / (2 : ℝ) ^ ε := by
      rw [sub_div, div_self (by positivity)]
    rw [← Real.log_rpow (by norm_num), rpow_neg (by norm_num), inv_eq_one_div (2 ^ ε), this]
    set c := (2 : ℝ) ^ ε
    have hc : 1 < c := by
      rw [← rpow_zero (2 : ℝ)]
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) εpos
    apply (div_lt_iff₀' (by positivity)).mpr <| lt_sub_iff_add_lt'.mp ?_
    let f := (fun x ↦ x * Real.log x - x)
    rw [(by simp [f] : -1 = f 1), (by simp [f] : c * Real.log c - c = f c)]
    have mono: StrictMonoOn f <| Ici 1 := by
      refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
      · apply continuousOn_id.mul (continuousOn_id.log ?_) |>.sub continuousOn_id
        intro x hx; simp only [mem_Ici] at hx; simp only [id_eq, ne_eq]; linarith
      · intro x hx; simp only [nonempty_Iio, interior_Ici', mem_Ioi] at hx
        dsimp only [f]
        rw [deriv_fun_sub, deriv_fun_mul, Real.deriv_log, deriv_id'', one_mul, mul_inv_cancel₀]
        · simp [log_pos hx]
        · linarith
        · simp only [differentiableAt_fun_id]
        · simp only [differentiableAt_log_iff, ne_eq]; linarith
        · exact differentiableAt_fun_id.mul <| differentiableAt_fun_id.log (by linarith)
        · simp only [differentiableAt_fun_id]
    exact mono (by rw [mem_Ici]) (mem_Ici.mpr <| le_of_lt hc) hc
  have Smooth1Properties_above_aux2 {x y ε : ℝ} (hε : ε ∈ Ioo 0 1) (hy : y ∈ Ioc 0 1)
    (hx2 : 2 ^ ε < x) :
      2 < (x / y) ^ (1 / ε) := by
    obtain ⟨εpos, ε1⟩ := hε
    obtain ⟨ypos, y1⟩ := hy
    calc
      _ > (2 ^ ε / y) ^ (1 / ε) := ?_
      _ = 2 / y ^ (1 / ε) := ?_
      _ ≥ 2 / y := ?_
      _ ≥ 2 := ?_
    · rw [gt_iff_lt, div_rpow, div_rpow, lt_div_iff₀, mul_comm_div, div_self, mul_one]
      <;> try positivity
      · exact rpow_lt_rpow (by positivity) hx2 (by positivity)
      · exact LT.lt.le <| lt_trans (by positivity) hx2
    · rw [div_rpow, ← rpow_mul, mul_div_cancel₀ 1 <| ne_of_gt εpos, rpow_one] <;> positivity
    · have : y ^ (1 / ε) ≤ y := by
        nth_rewrite 2 [← rpow_one y]
        exact rpow_le_rpow_of_exponent_ge ypos y1 (by linarith [one_lt_one_div εpos ε1])
      have pos : 0 < y ^ (1 / ε) := rpow_pos_of_pos ypos _
      rw [ge_iff_le, div_le_iff₀, div_mul_eq_mul_div, le_div_iff₀', mul_comm] <;> try linarith
    · rw [ge_iff_le, le_div_iff₀ <| ypos]; exact (mul_le_iff_le_one_right zero_lt_two).mpr y1
  have deltaSpikeSupport {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
      (suppν : ν.support ⊆ Icc (1 / 2) 2) :
      DeltaSpike ν ε x ≠ 0 → x ∈ Icc (2 ^ (-ε)) (2 ^ ε) := by
    intro h
    have heq : (fun z ↦ if z < 0 then 0 else DeltaSpike ν ε z) x =
        DeltaSpike ν ε x := by simp [xnonneg]
    rw [← heq] at h
    exact (Function.support_subset_iff.mp <| DeltaSpikeSupport_aux εpos suppν) _ h
  set c := 2 * Real.log 2; use c
  constructor
  · simp only [c, zero_lt_two, mul_pos_iff_of_pos_left]; exact log_pos (by norm_num)
  constructor
  · rfl
  intro ε x hε hx
  have hx2 : 2 ^ ε < x := by
    calc
      x ≥ 1 + (2 * Real.log 2) * ε := hx
      _ > 2 ^ ε := ?_
    refine lt_add_of_sub_left_lt <| (div_lt_iff₀ hε.1).mp ?_
    calc
      2 * Real.log 2 > 2 * (1 - 2 ^ (-ε)) / ε := ?_
      _ > 2 ^ ε * (1 - 2 ^ (-ε)) / ε := ?_
      _ = (2 ^ ε - 1) / ε := ?_
    · field_simp
      exact Smooth1Properties_estimate hε.1
    · have : (2 : ℝ) ^ ε < 2 := by
        have h := rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) hε.2
        rwa [Real.rpow_one] at h
      have pos : 0 < (1 - 2 ^ (-ε)) / ε := by
        refine div_pos ?_ hε.1
        rw [sub_pos]
        have h := rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num)
          (neg_lt_zero.mpr hε.1)
        rwa [Real.rpow_zero] at h
      have := (mul_lt_mul_iff_left₀ pos).mpr this
      ring_nf at this ⊢
      exact this
    · have : (2 : ℝ) ^ ε * (2 : ℝ) ^ (-ε) = (2 : ℝ) ^ (ε - ε) := by
        rw [← rpow_add (by norm_num), add_neg_cancel, sub_self]
      conv => lhs; lhs; ring_nf; rhs; simp [this]
  unfold Smooth1 MellinConvolution
  simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  have ypos := mem_Ioi.mp hy
  by_cases y1 : y ≤ 1
  swap
  · simp [ypos, y1]
  simp only [mem_Ioi.mp hy, y1, and_self, ↓reduceIte, div_eq_zero_iff]; left
  have hNonneg : 0 ≤ x / y := by
    apply div_nonneg
    · exact (le_trans (rpow_pos_of_pos (by norm_num) ε).le hx2.le)
    · exact ypos.le
  have hOutside : x / y ∉ Icc (2 ^ (-ε)) (2 ^ ε) := by
    intro hMem
    have hUpper : x / y ≤ 2 ^ ε := (mem_Icc.mp hMem).2
    have hStrict : 2 ^ ε < x / y := by
      have hPow : x / y = ((x / y) ^ (1 / ε)) ^ ε := by
        rw [← rpow_mul]
        simp only [one_div, inv_mul_cancel₀ (ne_of_gt hε.1), rpow_one]
        exact hNonneg
      rw [hPow]
      refine rpow_lt_rpow (by norm_num) ?_ hε.1
      exact Smooth1Properties_above_aux2 hε ⟨ypos, y1⟩ hx2
    exact not_lt_of_ge hUpper hStrict
  by_contra hNZ
  exact hOutside (deltaSpikeSupport hε.1 hNonneg suppν hNZ)





set_option backward.isDefEq.respectTransparency false in
lemma MellinOfSmooth1a {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s =
      s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by
  have hSym {𝕂 : Type} [RCLike 𝕂] (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
      MellinConvolution f g x = MellinConvolution g f x := by
    have hMul (h : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
        ∫ y in Ioi 0, h (y * a) / y = ∫ y in Ioi 0, h y / y := by
      have hh := integral_comp_mul_right_Ioi (fun y ↦ h y / y) 0 ha
      simp only [RCLike.ofReal_mul, zero_mul, eq_inv_smul_iff₀ (ne_of_gt ha)] at hh
      rw [← integral_smul] at hh
      rw [← hh, setIntegral_congr_fun (by simp)]
      intro _ _
      simp only [RCLike.real_smul_eq_coe_mul]
      rw [mul_comm (a : 𝕂), div_mul, mul_div_assoc, div_self ?_, mul_one]
      exact (RCLike.ofReal_ne_zero).mpr <| ne_of_gt ha
    have hInv (h : ℝ → 𝕂) :
        ∫ y in Ioi 0, h (1 / y) / y = ∫ y in Ioi 0, h y / y := by
      have hh := integral_comp_rpow_Ioi (fun y ↦ h y / y) (p := -1) (by simp)
      rw [← hh, setIntegral_congr_fun (by simp)]
      intro y hy
      have : (y : 𝕂) ≠ 0 := (RCLike.ofReal_ne_zero).mpr <| LT.lt.ne' hy
      simp only [abs_neg, abs_one, rpow_neg_one, map_inv₀, div_inv_eq_mul,
        RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]
      ring_nf
      simp [field]
    unfold MellinConvolution
    calc
      _ = ∫ y in Ioi 0, f (y * x) * g (1 / y) / y := ?_
      _ = _ := ?_
    · rw [← hMul (fun y ↦ f y * g (x / y)) xpos]
      simp [div_mul_cancel_right₀ <| ne_of_gt xpos]
    · convert (hInv fun y ↦ f (y * x) * g (1 / y)).symm using 3
      rw [one_div_one_div, mul_comm, mul_comm_div, one_mul]
  have DeltaSpikeSupport_aux {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
      (suppν : ν.support ⊆ Icc (1 / 2) 2) :
      (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x).support ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
    unfold DeltaSpike
    simp only [one_div, Function.support_subset_iff, ne_eq, ite_eq_left_iff, not_lt, div_eq_zero_iff,
      not_forall, exists_prop, mem_Icc, and_imp]
    intro x hx h; push Not at h
    have := suppν <| Function.mem_support.mpr h.1
    simp only [one_div, mem_Icc] at this
    have hl := (le_rpow_inv_iff_of_pos (by norm_num) hx εpos).mp this.1
    rw [inv_rpow (by norm_num) ε, ← rpow_neg (by norm_num)] at hl
    refine ⟨hl, (rpow_inv_le_iff_of_pos ?_ (by norm_num) εpos).mp this.2⟩
    linarith [(by apply rpow_nonneg (by norm_num) : 0 ≤ (2 : ℝ) ^ (-ε))]
  have MellinConvolutionTransform (f g : ℝ → ℂ) (s : ℂ)
      (hf : IntegrableOn (fun x y ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)).uncurry
        (Ioi 0 ×ˢ Ioi 0)) :
      𝓜 (MellinConvolution f g) s = 𝓜 f s * 𝓜 g s := by
    dsimp [mellin, MellinConvolution]
    set f₁ : ℝ × ℝ → ℂ :=
      fun ⟨x, y⟩ ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)
    calc
      _ = ∫ (x : ℝ) in Ioi 0, ∫ (y : ℝ) in Ioi 0, f₁ (x, y) := ?_
      _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f₁ (x, y) := by
          refine integral_integral_swap
            (μ := volume.restrict (Ioi 0))
            (ν := volume.restrict (Ioi 0)) ?_
          simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod]
            using hf
      _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
          f y * g (x / y) / ↑y * ↑x ^ (s - 1) := rfl
      _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
          f y * g (x * y / y) / ↑y * ↑(x * y) ^ (s - 1) * y := ?_
      _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
          f y * ↑y ^ (s - 1) * (g x * ↑x ^ (s - 1)) := ?_
      _ = ∫ (y : ℝ) in Ioi 0,
          f y * ↑y ^ (s - 1) * ∫ (x : ℝ) in Ioi 0, g x * ↑x ^ (s - 1) := ?_
      _ = _ := integral_mul_const _ _
    <;> try (rw [setIntegral_congr_fun (by simp)]; intro y hy; simp only [ofReal_mul])
    · simp only [integral_mul_const, f₁, mul_comm]
    · simp only [integral_mul_const]
      have := integral_comp_mul_right_Ioi
        (fun x ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)) 0 hy
      have y_ne_zeroℂ : (y : ℂ) ≠ 0 := slitPlane_ne_zero (Or.inl hy)
      field_simp at this ⊢
      simp only [ofReal_mul, one_div, mul_zero, real_smul, ofReal_inv, field] at this ⊢
      rw [← this]
      field_simp
      congr with x
      ring_nf
    · rw [setIntegral_congr_fun (by simp)]
      intro x hx
      have y_ne_zeroℝ : y ≠ 0 := ne_of_gt (mem_Ioi.mp hy)
      have y_ne_zeroℂ : (y : ℂ) ≠ 0 := by exact_mod_cast y_ne_zeroℝ
      field_simp
      rw [mul_cpow_ofReal_nonneg hy.le hx.le]
      ring
    · apply integral_const_mul
    · congr <;> ext <;> ring
  have deltaSpikeSupport {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
      (suppν : ν.support ⊆ Icc (1 / 2) 2) :
      DeltaSpike ν ε x ≠ 0 → x ∈ Icc (2 ^ (-ε)) (2 ^ ε) := by
    intro h
    have heq : (fun z ↦ if z < 0 then 0 else DeltaSpike ν ε z) x =
        DeltaSpike ν ε x := by simp [xnonneg]
    rw [← heq] at h
    exact (Function.support_subset_iff.mp <| DeltaSpikeSupport_aux εpos suppν) _ h
  have deltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
      (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
    apply diffν.continuous.comp (g := ν) _ |>.div_const
    exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le
  let f' : ℝ → ℂ := fun x ↦ DeltaSpike ν ε x
  let f : ℝ → ℂ := fun x ↦ DeltaSpike ν ε x / x
  let g : ℝ → ℂ := fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0
  let F : ℝ × ℝ → ℂ := Function.uncurry fun x y ↦ f y * g (x / y) * (x : ℂ) ^ (s - 1)
  let S := {⟨x, y⟩ : ℝ × ℝ | 0 < x  ∧ x ≤ y ∧ 2 ^ (-ε) ≤ y ∧ y ≤ 2 ^ ε}
  let F' : ℝ × ℝ → ℂ := piecewise S (fun ⟨x, y⟩ ↦ f y * (x : ℂ) ^ (s - 1))
     (fun _ ↦ 0)
  let Tx := Ioc 0 ((2 : ℝ) ^ ε)
  let Ty := Icc ((2 : ℝ) ^ (-ε)) ((2 : ℝ) ^ ε)

  have Seq : S = (Tx ×ˢ Ty) ∩ {(x, y) : ℝ × ℝ | x ≤ y} := by
    ext ⟨x, y⟩; constructor
    · exact fun h ↦ ⟨⟨⟨h.1, le_trans h.2.1 h.2.2.2⟩, ⟨h.2.2.1, h.2.2.2⟩⟩, h.2.1⟩
    · exact fun h ↦  ⟨h.1.1.1, ⟨h.2, h.1.2.1, h.1.2.2⟩⟩
  have SsubI : S ⊆ Ioi 0 ×ˢ Ioi 0 :=
    fun z hz ↦ ⟨hz.1, lt_of_lt_of_le (by apply rpow_pos_of_pos; norm_num) hz.2.2.1⟩
  have SsubT: S ⊆ Tx ×ˢ Ty := by simp_rw [Seq, inter_subset_left]
  have Smeas : MeasurableSet S := by
    rw [Seq]; apply MeasurableSet.inter ?_ <| measurableSet_le measurable_fst measurable_snd
    simp [measurableSet_prod, Tx, Ty]

  have int_F: IntegrableOn F (Ioi 0 ×ˢ Ioi 0) := by
    apply IntegrableOn.congr_fun (f := F') ?_ ?_ (by simp [measurableSet_prod]); swap
    · simp only [F, F', f, g, mul_ite, mul_one, mul_zero]
      intro ⟨x, y⟩ hz
      by_cases hS : ⟨x, y⟩ ∈ S <;> simp only [hS, piecewise]
      <;> simp only [mem_prod, mem_Ioi, mem_setOf_eq, not_and, not_le, S] at hz hS
      · simp [div_pos hz.1 hz.2, (div_le_one hz.2).mpr hS.2.1]
      · by_cases hxy : x / y ≤ 1
        swap
        · simp [hxy]
        have hy : y ∉ Icc (2 ^ (-ε)) (2 ^ ε) := by
          simp only [mem_Icc, not_and, not_le]; exact hS hz.1 <| (div_le_one hz.2).mp hxy
        have hDelta : DeltaSpike ν ε y = 0 := by
          by_contra hNZ
          exact hy (deltaSpikeSupport εpos hz.2.le suppν hNZ)
        simp [hDelta]
    · apply Integrable.piecewise Smeas ?_ integrableOn_zero
      simp only [IntegrableOn, Measure.restrict_restrict_of_subset SsubI]
      apply MeasureTheory.Integrable.mono_measure ?_
      · apply MeasureTheory.Measure.restrict_mono' SsubT.eventuallyLE le_rfl
      have : volume.restrict (Tx ×ˢ Ty) = (volume.restrict Tx).prod (volume.restrict Ty) := by
        rw [Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]
      conv => rw [this]; lhs; intro; rw [mul_comm]
      apply MeasureTheory.Integrable.mul_prod (f := fun x ↦ (x : ℂ) ^ (s - 1))
        (μ := Measure.restrict volume Tx)
      · simp only [Tx]
        rw [← IntegrableOn, integrableOn_Ioc_iff_integrableOn_Ioo,
          intervalIntegral.integrableOn_Ioo_cpow_iff]
        · simp [hs]
        · apply rpow_pos_of_pos (by norm_num)
      · apply (ContinuousOn.div ?_ ?_ ?_).integrableOn_compact isCompact_Icc
        · exact (continuous_ofReal.comp <| deltaSpikeContinuous εpos diffν).continuousOn
        · exact continuous_ofReal.continuousOn
        · intro x hx; simp only [mem_Icc] at hx; simp only [ofReal_ne_zero]
          linarith [(by apply rpow_pos_of_pos (by norm_num) : (0 : ℝ) < 2 ^ (-ε))]

  have : 𝓜 (MellinConvolution g f') s = 𝓜 g s * 𝓜 f' s := by
    rw [mul_comm, ← MellinConvolutionTransform f' g s
      (by
        refine int_F.congr_fun ?_ (by measurability)
        intro ⟨x, y⟩ _
        dsimp [F, f, f']
        ring)]
    dsimp [mellin]; rw [setIntegral_congr_fun (by simp)]
    intro x hx; simp_rw [hSym (𝕂 := ℂ) _ _ <| mem_Ioi.mp hx]

  convert! this using 1
  · congr; funext x; convert! integral_ofReal.symm
    simp only [MellinConvolution, RCLike.ofReal_div, ite_mul, one_mul, zero_mul, @apply_ite ℝ ℂ,
      algebraMap.coe_zero, g]; rfl
  · have hOne : 𝓜 ((fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0)) s = 1 / s := by
      convert (hasMellin_one_Ioc hs).right
      congr
    have hDelta : 𝓜 (fun x ↦ (DeltaSpike ν ε x : ℂ)) s =
        𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by
      unfold DeltaSpike
      push_cast
      rw [mellin_div_const, mellin_comp_rpow (fun x ↦ (ν x : ℂ)),
        abs_of_nonneg (by positivity)]
      simp only [one_div, inv_inv, ofReal_inv, div_inv_eq_mul, real_smul]
      rw [mul_div_cancel_left₀ _ (ne_zero_of_re_pos εpos)]
      ring_nf
    rw [hOne, hDelta]
    simp



lemma Smooth1ContinuousAt {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : SmoothingF.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y) :
    ContinuousAt (fun x ↦ Smooth1 SmoothingF ε x) y := by
  have hSym {𝕂 : Type} [RCLike 𝕂] (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
      MellinConvolution f g x = MellinConvolution g f x := by
    have hMul (h : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
        ∫ y in Ioi 0, h (y * a) / y = ∫ y in Ioi 0, h y / y := by
      have hh := integral_comp_mul_right_Ioi (fun y ↦ h y / y) 0 ha
      simp only [RCLike.ofReal_mul, zero_mul, eq_inv_smul_iff₀ (ne_of_gt ha)] at hh
      rw [← integral_smul] at hh
      rw [← hh, setIntegral_congr_fun (by simp)]
      intro _ _
      simp only [RCLike.real_smul_eq_coe_mul]
      rw [mul_comm (a : 𝕂), div_mul, mul_div_assoc, div_self ?_, mul_one]
      exact (RCLike.ofReal_ne_zero).mpr <| ne_of_gt ha
    have hInv (h : ℝ → 𝕂) :
        ∫ y in Ioi 0, h (1 / y) / y = ∫ y in Ioi 0, h y / y := by
      have hh := integral_comp_rpow_Ioi (fun y ↦ h y / y) (p := -1) (by simp)
      rw [← hh, setIntegral_congr_fun (by simp)]
      intro y hy
      have : (y : 𝕂) ≠ 0 := (RCLike.ofReal_ne_zero).mpr <| LT.lt.ne' hy
      simp only [abs_neg, abs_one, rpow_neg_one, map_inv₀, div_inv_eq_mul,
        RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]
      ring_nf
      simp [field]
    unfold MellinConvolution
    calc
      _ = ∫ y in Ioi 0, f (y * x) * g (1 / y) / y := ?_
      _ = _ := ?_
    · rw [← hMul (fun y ↦ f y * g (x / y)) xpos]
      simp [div_mul_cancel_right₀ <| ne_of_gt xpos]
    · convert (hInv fun y ↦ f (y * x) * g (1 / y)).symm using 3
      rw [one_div_one_div, mul_comm, mul_comm_div, one_mul]
  have DeltaSpikeSupport_aux {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
      (suppν : ν.support ⊆ Icc (1 / 2) 2) :
      (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x).support ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
    unfold DeltaSpike
    simp only [one_div, Function.support_subset_iff, ne_eq, ite_eq_left_iff, not_lt, div_eq_zero_iff,
      not_forall, exists_prop, mem_Icc, and_imp]
    intro x hx h; push Not at h
    have := suppν <| Function.mem_support.mpr h.1
    simp only [one_div, mem_Icc] at this
    have hl := (le_rpow_inv_iff_of_pos (by norm_num) hx εpos).mp this.1
    rw [inv_rpow (by norm_num) ε, ← rpow_neg (by norm_num)] at hl
    refine ⟨hl, (rpow_inv_le_iff_of_pos ?_ (by norm_num) εpos).mp this.2⟩
    linarith [(by apply rpow_nonneg (by norm_num) : 0 ≤ (2 : ℝ) ^ (-ε))]
  have deltaSpikeSupport {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
      (suppν : ν.support ⊆ Icc (1 / 2) 2) :
      DeltaSpike ν ε x ≠ 0 → x ∈ Icc (2 ^ (-ε)) (2 ^ ε) := by
    intro h
    have heq : (fun z ↦ if z < 0 then 0 else DeltaSpike ν ε z) x =
        DeltaSpike ν ε x := by simp [xnonneg]
    rw [← heq] at h
    exact (Function.support_subset_iff.mp <| DeltaSpikeSupport_aux εpos suppν) _ h
  have deltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
      (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
    apply diffν.continuous.comp (g := ν) _ |>.div_const
    exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le
  have deltaSpikeNonNeg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
      {x ε : ℝ} (xpos : 0 < x) (εpos : 0 < ε) :
      0 ≤ DeltaSpike ν ε x := by
    dsimp [DeltaSpike]
    have hx : 0 < x ^ (1 / ε) := by positivity
    have : 0 ≤ ν (x ^ (1 / ε)) := νnonneg _ hx
    positivity
  apply ContinuousAt.congr
    (f := (fun x ↦ MellinConvolution (DeltaSpike SmoothingF ε)
      (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) x)) _
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply hSym (𝕂 := ℝ) _ _ hx
  apply continuousAt_of_dominated (bound := (fun x ↦ 2 ^ ε * DeltaSpike SmoothingF ε x))
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · apply Measurable.mul
      · exact Continuous.measurable <| deltaSpikeContinuous εpos diffSmoothingF
      · apply Measurable.ite _ (by fun_prop) (by fun_prop)
        apply MeasurableSet.congr (s := Ici x) (by measurability)
        ext a
        constructor
        · intro ha
          have apos : 0 < a := lt_of_lt_of_le hx ha
          constructor
          · exact div_pos hx apos
          · exact (div_le_one apos).mpr ha
        · intro ha
          have : 0 < a := (div_pos_iff_of_pos_left hx).mp ha.1
          exact (div_le_one this).mp ha.2
    · fun_prop
  · filter_upwards [lt_mem_nhds ypos] with x hx
    filter_upwards [ae_restrict_mem (by measurability)] with t ht
    simp only [mul_ite, mul_one, mul_zero, RCLike.ofReal_real_eq_id, id_eq, norm_div, norm_eq_abs]
    by_cases! h : DeltaSpike SmoothingF ε t = 0
    · simp [h]
    have := deltaSpikeSupport εpos ht.le suppSmoothingF h
    have dsnonneg : 0 ≤ DeltaSpike SmoothingF ε t := by
      apply deltaSpikeNonNeg <;> assumption
    calc
      _ ≤ |DeltaSpike SmoothingF ε t| / |t| := by
        gcongr
        · split_ifs with h
          · apply le_refl
          · exact dsnonneg
      _ ≤ _ := by
        rw [_root_.abs_of_nonneg dsnonneg, mul_comm, div_eq_mul_one_div, _root_.abs_of_pos ht]
        gcongr
        apply (one_div_le ht (by bound)).mpr
        · convert this.1 using 1
          rw [div_eq_iff (by positivity), ← rpow_add (by norm_num), neg_add_cancel, rpow_zero]
  · apply Integrable.const_mul
    apply (integrable_indicator_iff (by measurability)).mp
    apply (integrableOn_iff_integrable_of_support_subset (s := Icc (2 ^ (-ε)) (2 ^ ε)) _).mp
    · apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply ContinuousOn.congr  (f := DeltaSpike SmoothingF ε)
      · apply Continuous.continuousOn
        apply deltaSpikeContinuous<;> assumption
      · intro x hx
        have : x ∈ Ioi 0 := by
          apply mem_Ioi.mpr
          apply lt_of_lt_of_le (by bound) hx.1
        rw [indicator, if_pos this]
    · unfold indicator
      simp_rw [mem_Ioi]
      apply Function.support_subset_iff.mpr
      simp only [ne_eq, ite_eq_right_iff, Classical.not_imp, mem_Icc, and_imp]
      intro x hx
      apply deltaSpikeSupport εpos hx.le suppSmoothingF
  · have : ∀ᵐ (a : ℝ) ∂volume.restrict (Ioi 0), a ≠ y := by
      apply ae_iff.mpr
      simp
    filter_upwards [ae_restrict_mem (by measurability), this] with x hx hx2
    simp only [mem_Ioi] at hx
    apply ContinuousAt.div_const
    apply ContinuousAt.mul (by fun_prop)
    have : (fun x_1 ↦ if 0 < x_1 / x ∧ x_1 / x ≤ 1 then 1 else 0) =
        (Ioc 0 x).indicator (fun _ ↦ (1 : ℝ)) := by
      ext t
      unfold indicator
      simp [div_pos_iff_of_pos_right, div_le_one₀, hx]
    rw [this]
    apply ContinuousOn.continuousAt_indicator (by fun_prop)
    simp [frontier_Ioc hx, ypos.ne', hx2.symm]
