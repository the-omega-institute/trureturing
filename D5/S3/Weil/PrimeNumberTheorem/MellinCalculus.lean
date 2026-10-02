/- GID: D5/S3/Weil/PrimeNumberTheorem/MellinCalculus
   generality: G
   mirror-B: D5/B/S3/Weil/PrimeNumberTheorem/MellinCalculus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compactly supported Mellin kernels have uniform vertical-strip decay. -/

/-
Source: AlexKontorovich/PrimeNumberTheoremAnd, revision 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01.
Original file: PrimeNumberTheoremAnd/MellinCalculus.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0.
Full license and upstream attribution: Library/Weil/primenumbertheoremand2026medium.md.
This file is modified from the cited source.
Retirement: replace this consumed closure with direct references when this
repository's adopted Mathlib revision contains equivalent quantified contracts.
-/

import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import D5.S3.Weil.ZetaPntBase.Auxiliary

open scoped ContDiff

set_option lang.lemmaCmd true


open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

local notation (name := mellintransform) "𝓜" => mellin


noncomputable def MellinConvolution (f g : ℝ → 𝕂) (x : ℝ) : 𝕂 :=
  ∫ y in Ioi 0, f y * g (x / y) / y


-- filter-free version:
set_option backward.isDefEq.respectTransparency false in
lemma MellinOfPsi {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ C > 0, ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
    ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
  have MellinOfPsi_aux {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
      (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
      {s : ℂ} (hs : s ≠ 0) :
      ∫ (x : ℝ) in Ioi 0, (ν x) * (x : ℂ) ^ (s - 1) =
      - (1 / s) * ∫ (x : ℝ) in Ioi 0, (deriv ν x) * (x : ℂ) ^ s := by
    have hMulSupp {u : Set ℝ} {f g : ℝ → ℂ} (hf : f.support ⊆ u) :
        (f * g).support ⊆ u := by
      simp_rw [Function.support_mul', inter_subset, subset_union_of_subset_right hf]
    have hDerivSupp {a b : ℝ} {f : ℝ → ℂ} (hf : f.support ⊆ Icc a b) :
        (deriv f).support ⊆ Icc a b := by
      have h := support_deriv_subset (f := fun x ↦ f x)
      dsimp [tsupport] at h
      have h' := subset_trans h (closure_mono hf)
      rwa [closure_Icc] at h'
    have hZero {a b : ℝ} (f : ℝ → ℂ) (ha : 0 < a)
        (hf : f.support ⊆ Icc a b) : Tendsto f (𝓝[>]0) (𝓝 0) := by
      apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
      filter_upwards [Ioo_mem_nhdsGT ha] with c hc
      have hc' := (mem_Ioo.mp hc).2
      have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
      convert mt (Function.support_subset_iff.mp hf c) h <;> simp
    have hTop {a b : ℝ} (f : ℝ → ℂ)
        (hf : f.support ⊆ Icc a b) : Tendsto f atTop (𝓝 0) := by
      apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
      filter_upwards [Ioi_mem_atTop b] with c hc
      rw [mem_Ioi] at hc
      have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
      convert mt (Function.support_subset_iff.mp hf c) h <;> simp
    have hIBP {a b : ℝ} (f g : ℝ → ℂ) (ha : 0 < a) (hab : a ≤ b)
        (hf : f.support ⊆ Icc a b)
        (fDiff : DifferentiableOn ℝ f (Ioi 0))
        (gDiff : DifferentiableOn ℝ g (Ioi 0))
        (fderivCont : ContinuousOn (deriv f) (Ioi 0))
        (gderivCont : ContinuousOn (deriv g) (Ioi 0)) :
        ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
      have Icc_sub : Icc a b ⊆ Ioi 0 := (Icc_subset_Ioi_iff hab).mpr ha
      have fderivSupp := hDerivSupp hf
      have fgSupp : (f * g).support ⊆ Icc a b := hMulSupp hf
      have fDerivgInt : IntegrableOn (f * deriv g) (Ioi 0) := by
        apply (integrableOn_iff_integrable_of_support_subset (hMulSupp hf)).mp
        exact fDiff.continuousOn.mono Icc_sub |>.mul
          (gderivCont.mono Icc_sub) |>.integrableOn_Icc
      have gDerivfInt : IntegrableOn (deriv f * g) (Ioi 0) := by
        apply (integrableOn_iff_integrable_of_support_subset (hMulSupp fderivSupp)).mp
        exact fderivCont.mono Icc_sub |>.mul
          (gDiff.continuousOn.mono Icc_sub) |>.integrableOn_Icc
      have lim_at_zero : Tendsto (f * g) (𝓝[>]0) (𝓝 0) := hZero (f * g) ha fgSupp
      have lim_at_inf : Tendsto (f * g) atTop (𝓝 0) := hTop (f * g) fgSupp
      simpa using integral_Ioi_mul_deriv_eq_deriv_mul
        (fun x hx ↦ fDiff.hasDerivAt (Ioi_mem_nhds hx))
        (fun x hx ↦ gDiff.hasDerivAt (Ioi_mem_nhds hx))
        fDerivgInt gDerivfInt lim_at_zero lim_at_inf
    let g (s : ℂ) := fun (x : ℝ)  ↦ x ^ s / s
    have gderiv {s : ℂ} (hs : s ≠ 0) {x: ℝ} (hx : x ∈ Ioi 0) :
        deriv (g s) x = x ^ (s - 1) := by
      have := HasDerivAt.cpow_const (c := s) (hasDerivAt_id (x : ℂ)) (Or.inl hx)
      simp_rw [mul_one, id_eq] at this
      rw [deriv_div_const, deriv.comp_ofReal (e := fun x ↦ x ^ s)]
      · rw [this.deriv, mul_div_right_comm, div_self hs, one_mul]
      · apply hasDerivAt_deriv_iff.mp
        simp only [this.deriv, this]
    calc
      _ =  ∫ (x : ℝ) in Ioi 0, ↑(ν x) * deriv (@g s) x := ?_
      _ = -∫ (x : ℝ) in Ioi 0, deriv (fun x ↦ ↑(ν x)) x * @g s x := ?_
      _ = -∫ (x : ℝ) in Ioi 0, deriv ν x * @g s x := ?_
      _ = -∫ (x : ℝ) in Ioi 0, deriv ν x * x ^ s / s := by simp only [mul_div, g]
      _ = _ := ?_
    · rw [setIntegral_congr_fun (by simp)]
      intro _ hx
      simp only [gderiv hs hx]
    · apply hIBP (ν ·) (g s)
        (a := 1 / 2) (b := 2) (by norm_num) (by norm_num)
      · simpa only [Function.support_subset_iff, ne_eq, ofReal_eq_zero]
      · exact (Differentiable.ofReal_comp_iff.mpr
          (diffν.differentiable (by norm_num))).differentiableOn
      · refine DifferentiableOn.div_const ?_ s
        intro a ha
        refine DifferentiableAt.comp_ofReal (e := fun x ↦ x ^ s) ?_ |>.differentiableWithinAt
        apply differentiableAt_fun_id.cpow (differentiableAt_const s) <| by exact Or.inl ha
      · have hDeriv : deriv (fun x : ℝ ↦ (ν x : ℂ)) =
            (fun x ↦ ((deriv ν) x : ℂ)) := by
          funext x
          exact deriv.ofReal_comp
        simp only [hDeriv]
        exact continuous_ofReal.comp (diffν.continuous_deriv (by norm_num)) |>.continuousOn
      · apply ContinuousOn.congr (f := fun (x : ℝ) ↦ (x : ℂ) ^ (s - 1)) ?_
          fun x hx ↦ gderiv hs hx
        exact continuous_ofReal.continuousOn.cpow continuousOn_const
          (fun x hx ↦ Complex.ofReal_mem_slitPlane.mpr (mem_Ioi.mp hx))
    · congr; funext; congr
      apply (hasDerivAt_deriv_iff.mpr ?_).ofReal_comp.deriv
      exact diffν.contDiffAt.differentiableAt (by norm_num)
    · simp only [neg_mul, neg_inj]
      conv => lhs; rhs; intro; rw [← mul_one_div, mul_comm]
      rw [integral_const_mul]
  let f := fun (x : ℝ) ↦ ‖deriv ν x‖
  have cont : ContinuousOn f (Icc (1 / 2) 2) :=
    (Continuous.comp (by continuity) <| diffν.continuous_deriv (by norm_num)).continuousOn
  obtain ⟨a, _, max⟩ := isCompact_Icc.exists_isMaxOn (f := f) (by norm_num) cont
  let σ₂ : ℝ := 2
  let C : ℝ := f a * 2 ^ σ₂ * (3 / 2)
  have mainBnd : ∀ (σ₁ : ℝ), 0 < σ₁ → ∀ (s : ℂ), σ₁ ≤ s.re → s.re ≤ 2 →
      ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
    intro σ₁ σ₁pos s hs₁ hs₂
    have s_ne_zero: s ≠ 0 := fun h ↦ by linarith [zero_re ▸ h ▸ hs₁]
    simp only [mellin, f, MellinOfPsi_aux diffν suppν s_ne_zero, norm_mul, smul_eq_mul, mul_comm]
    gcongr
    · simp
    calc
      _ ≤ ∫ (x : ℝ) in Ioi 0, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ = ∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ ≤ ‖∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖‖ :=
          le_abs_self _
      _ ≤ _ := ?_
    · simp_rw [norm_integral_le_integral_norm]
    · have hsupport :
          (fun x : ℝ ↦ ‖deriv ν x * (x : ℂ) ^ s‖).support ⊆ Icc (1 / 2) 2 := by
        have hAbs (h : ℝ → ℂ) : (fun x ↦ ‖h x‖).support = h.support := by
          simp only [Function.support, ne_eq]
          simp_rw [norm_ne_zero_iff]
        have hOfReal (h : ℝ → ℝ) :
            (fun x ↦ (h x : ℂ)).support = h.support := by
          apply Function.support_comp_eq (g := ofReal)
          simp
        have hDerivSupp : (deriv ν).support ⊆ Icc (1 / 2) 2 := by
          have h := support_deriv_subset (f := ν)
          dsimp [tsupport] at h
          have h' := subset_trans h (closure_mono suppν)
          rwa [closure_Icc] at h'
        simp only [hAbs, Function.support_mul, hOfReal]
        exact (inter_subset_left.trans hDerivSupp)
      have h : ∫ (x : ℝ) in Ioi 0, ‖deriv ν x * (x : ℂ) ^ s‖ =
          ∫ (x : ℝ) in Ioi 0 ∩ Icc (1 / 2) 2, ‖deriv ν x * (x : ℂ) ^ s‖ := by
        rw [← setIntegral_indicator measurableSet_Icc, indicator_eq_self.2 hsupport]
      rwa [inter_eq_self_of_subset_right
        ((Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num))] at h
    · have hIcc : ∀ x ∈ Icc (1 / 2 : ℝ) 2,
          ‖f x * ‖(x : ℂ) ^ s‖‖ ≤ f a * 2 ^ σ₂ := by
        intro x hx
        have f_bound := isMaxOn_iff.mp max x hx
        have pow_bound : ‖(x : ℂ) ^ s‖ ≤ 2 ^ σ₂ := by
          rw [norm_cpow_eq_rpow_re_of_pos (by linarith [mem_Icc.mp hx])]
          have xpos : 0 ≤ x := by linarith [(mem_Icc.mp hx).1]
          have h := rpow_le_rpow xpos (mem_Icc.mp hx).2 (by linarith : 0 ≤ s.re)
          exact le_trans h <| rpow_le_rpow_of_exponent_le (by norm_num) hs₂
        convert! mul_le_mul f_bound pow_bound (norm_nonneg _) ?_ using 1 <;> simp [f]
      have hab : (1 / 2 : ℝ) ≤ 2 := by norm_num
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := f a * 2 ^ σ₂) (f := fun x ↦ f x * ‖(x : ℂ) ^ s‖)
        (a := (1 / 2 : ℝ)) (b := 2)
        (fun x hx ↦ hIcc x (mem_Icc_of_Ioc (uIoc_of_le hab ▸ hx)))
      simp only [Real.norm_eq_abs, norm_real, norm_mul] at this ⊢
      rwa [(by norm_num: |(2 : ℝ) - 1 / 2| = 3 / 2),
        intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at this
  have Cnonneg : 0 ≤ C := by
    have hh := mainBnd 1 (by norm_num) ((3 : ℂ) / 2) (by norm_num) (by norm_num)
    have hhh : 0 ≤ ‖𝓜 (fun x ↦ (ν x : ℂ)) ((3 : ℂ) / 2)‖ := by positivity
    have hhhh : 0 < ‖(3 : ℂ) / 2‖⁻¹ := by norm_num
    have := hhh.trans hh
    exact (mul_nonneg_iff_of_pos_right hhhh).mp this
  by_cases CeqZero : C = 0
  · refine ⟨1, by linarith, ?_⟩
    intro ε εpos s hs₁ hs₂
    have := mainBnd ε εpos s hs₁ hs₂
    rw [CeqZero, zero_mul] at this
    have : 0 ≤ 1 * ‖s‖⁻¹ := by positivity
    linarith
  · exact ⟨C, lt_of_le_of_ne Cnonneg fun a ↦ CeqZero (id (Eq.symm a)), mainBnd⟩




noncomputable def DeltaSpike (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ν (x ^ (1 / ε)) / ε
