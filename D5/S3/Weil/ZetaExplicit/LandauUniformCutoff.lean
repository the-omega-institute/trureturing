/- GID: D5/S3/Weil/ZetaExplicit/LandauUniformCutoff
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaExplicit/LandauUniformCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual inclusive positive zeta zero cutoff has a uniform Landau bound under RH. -/

import D5.S3.Weil.ZetaExplicit.GoodHeights
import D5.S3.Weil.Mertens.Cryptids.HorizontalBounds.Integral
import D5.S3.Weil.ZetaExplicit.LandauLeftVertical
import D5.S3.Weil.ZetaExplicit.LandauRightVertical
import D5.S3.Weil.ZetaAnalytic.RectangleLogDeriv
import D5.S3.Weil.Mertens.Cryptids.DigammaBinet
import D5.S3.Weil.Mertens.Cryptids.VonMangoldtCount.Foundation
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHHarmonicPairMoment

/-! The finite Landau contour estimate for the actual multiplicity-weighted zeta spectrum. -/

namespace D5.S3.Weil.ZetaExplicit.LandauUniformCutoff

open Complex Set MeasureTheory
open scoped Real
open Zeta23 Zeta23.Analytic
open ConjectureMachines.Semantics.Riemann.VonMangoldtCount
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
open D5.S3.Weil.DirichletPolynomialMeanSquare
open ConjectureMachines.Semantics.Riemann.HorizontalBounds

private theorem rh_re_eq_half (rh : RiemannHypothesis) {s : ℂ}
    (him : 0 < s.im) (hz : riemannZeta s = 0) : s.re = 1 / 2 := by
  have h1 : s ≠ 1 := by
    intro he
    simp [he] at him
  have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    simp [hn, mul_im, add_im] at him
  exact rh s hz htriv h1

private theorem six_lt_height (rh : RiemannHypothesis) {s : ℂ}
    (him : 0 < s.im) (hz : riemannZeta s = 0) : 6 < s.im := by
  have h := six_lt_abs_im_of_riemannZeta_eq_zero_of_re_eq_half (rh_re_eq_half rh him hz) hz
  rwa [abs_of_pos him] at h

private theorem no_zeros_height_one (rh : RiemannHypothesis) {s : ℂ}
    (him : s.im = 1) : riemannZeta s ≠ 0 := by
  intro hz
  have h := six_lt_height rh (by rw [him]; norm_num) hz
  norm_num [him] at h

/-- At a zero-free height the contour uses the same inclusive cutoff as the harmonic score. -/
private theorem landau_rectangle_eq_actual_cutoff (rh : RiemannHypothesis) {x c V : ℝ}
    (hx : 1 < x) (hc : 1 < c) (hV : 1 ≤ V)
    (htop : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) c, riemannZeta ((σ : ℂ) + V * I) ≠ 0) :
    RectangleIntegral' (fun s => (x : ℂ) ^ s * logDeriv riemannZeta s)
        ((-1 / 4 : ℂ) + I) ((c : ℂ) + V * I) =
      ∑ j ∈ positiveCutoff rh V, (zeroMult j.val : ℂ) * (x : ℂ) ^ j.val := by
  classical
  let z : ℂ := (-1 / 4 : ℂ) + I
  let w : ℂ := (c : ℂ) + V * I
  let emb : PositiveZetaZero ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  let zeros := (positiveCutoff rh V).map emb
  have hz_re : z.re = -1 / 4 := by norm_num [z]
  have hz_im : z.im = 1 := by norm_num [z]
  have hw_re : w.re = c := by simp [w]
  have hw_im : w.im = V := by simp [w]
  have hre : z.re ≤ w.re := by rw [hz_re, hw_re]; linarith
  have him : z.im ≤ w.im := by rwa [hz_im, hw_im]
  have hmem (s : ℂ) : s ∈ Rectangle z w ↔
      (-1 / 4 : ℝ) ≤ s.re ∧ s.re ≤ c ∧ (1 : ℝ) ≤ s.im ∧ s.im ≤ V := by
    rw [mem_Rect hre him s, hz_re, hz_im, hw_re, hw_im]
  have hcut (j : PositiveZetaZero) : j ∈ positiveCutoff rh V ↔ j.val.im ≤ V :=
    RHHarmonicPairMoment.cutoff_mem rh V j
  have hsub : (zeros : Set ℂ) ⊆ Rectangle z w := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hs)
    rw [hmem]
    change (-1 / 4 : ℝ) ≤ j.val.re ∧ j.val.re ≤ c ∧ 1 ≤ j.val.im ∧ j.val.im ≤ V
    have hr := rh_re_eq_half rh j.property.2 j.property.1.1
    exact ⟨by rw [hr]; norm_num, by rw [hr]; linarith,
      by linarith [six_lt_height rh j.property.2 j.property.1.1], (hcut j).mp hj⟩
  have hof_zero (s : ℂ) (hs : s ∈ Rectangle z w) : riemannZeta s = 0 ↔ s ∈ zeros := by
    constructor
    · intro hsz
      have hsi := (hmem s).mp hs
      have hpos : 0 < s.im := zero_lt_one.trans_le hsi.2.2.1
      have hre := rh_re_eq_half rh hpos hsz
      let j : PositiveZetaZero :=
        ⟨s, ⟨hsz, by rw [hre]; norm_num, by rw [hre]; norm_num⟩, hpos⟩
      exact Finset.mem_map.mpr ⟨j, (hcut j).mpr hsi.2.2.2, rfl⟩
    · intro hs
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hs
      exact j.property.1.1
  have hborder (s : ℂ) (hs : s ∈ RectangleBorder z w) : riemannZeta s ≠ 0 := by
    have hr := (hmem s).mp (rectangleBorder_subset_rectangle z w hs)
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
      hz_re, hz_im, hw_re, hw_im] at hs
    rcases hs with ((hb | hl) | ht) | hright
    · exact no_zeros_height_one rh hb.2
    · have hEq : s = (-1 / 4 : ℂ) + s.im * I := by apply Complex.ext <;> simp [hl.1]
      rw [hEq]
      exact ConjectureMachines.Semantics.Riemann.DigammaBinet.riemannZeta_leftVertical_ne_zero _
    · have hEq : s = (s.re : ℂ) + V * I := by apply Complex.ext <;> simp [ht.2]
      rw [hEq]
      exact htop _ ⟨hr.1, hr.2.1⟩
    · exact riemannZeta_ne_zero_of_one_lt_re (hright.1.symm ▸ hc)
  have hzeta : AnalyticOnNhd ℂ riemannZeta (Rectangle z w) := by
    intro s hs
    have hi := (hmem s).mp hs
    refine analyticOn_riemannZeta s ?_
    intro he
    have h := hi.2.2.1
    have he' : s = 1 := Set.mem_singleton_iff.mp he
    norm_num [he'] at h
  have hxp : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
  have hd : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
    differentiable_id.const_cpow (Or.inl hxp)
  have han : AnalyticOnNhd ℂ (fun s : ℂ => (x : ℂ) ^ s) (Rectangle z w) :=
    fun s _ => hd.analyticAt s
  change RectangleIntegral' (fun s => (x : ℂ) ^ s * logDeriv riemannZeta s) z w = _
  rw [rectangleIntegral'_mul_logDeriv hre him hzeta han hborder zeros hof_zero hsub]
  rw [Finset.sum_map]
  rfl


private theorem norm_integral_landau_bottom (rh : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x c : ℝ}, 1 < x → -1 / 4 ≤ c → c ≤ 2 →
      ‖∫ σ in (-1 / 4 : ℝ)..c, (x : ℂ) ^ ((σ : ℂ) + I) *
        (-logDeriv riemannZeta ((σ : ℂ) + I))‖ ≤ C * (c + 1 / 4) * x ^ c := by
  let s (σ : ℝ) : ℂ := (σ : ℂ) + I
  have hconts : Continuous s := by unfold s; fun_prop
  have hnonzero (σ : ℝ) : riemannZeta (s σ) ≠ 0 := no_zeros_height_one rh (by simp [s])
  have hzeta (σ : ℝ) : AnalyticAt ℂ riemannZeta (s σ) := by
    apply analyticOn_riemannZeta
    intro h
    have he := congrArg Complex.im (Set.mem_singleton_iff.mp h)
    simp [s] at he
  let f (σ : ℝ) : ℂ := logDeriv riemannZeta (s σ)
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun σ => by
    change ContinuousAt ((fun z => logDeriv riemannZeta z) ∘ s) σ
    simp only [logDeriv_apply]
    exact ((hzeta σ).deriv.continuousAt.div (hzeta σ).continuousAt (hnonzero σ)).comp
      hconts.continuousAt
  have hcompact : IsCompact (Set.Icc (-1 / 4 : ℝ) 2) := isCompact_Icc
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun {x c} hx hcl hcu => ?_⟩
  let g (σ : ℝ) := (x : ℂ) ^ (s σ) * (-f σ)
  have hle (σ : ℝ) (hσ : σ ∈ Set.uIoc (-1 / 4 : ℝ) c) : ‖g σ‖ ≤ x ^ c * max 1 B := by
    rw [Set.uIoc_of_le hcl] at hσ
    have hm : σ ∈ Set.Icc (-1 / 4 : ℝ) 2 := ⟨hσ.1.le, hσ.2.trans hcu⟩
    dsimp only [g]
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
    have he : (s σ).re = σ := by simp [s]
    rw [he]
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx.le hσ.2) ((hB σ hm).trans (le_max_right _ _))
      (norm_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hle
  rw [abs_of_nonneg (by linarith : 0 ≤ c - -1 / 4)] at hi
  convert hi using 1
  ring

private theorem sqrt_mul_square_log_absorb {x V : ℝ} (hx : 1 ≤ x) (hV : 1 ≤ V) :
    Real.sqrt x * Real.log (V + 9) ^ 2 ≤
      169 * (V + Real.sqrt x * (1 + Real.log x)^2) := by
  have hV0 : 0 < V := zero_lt_one.trans_le hV
  have hlognonneg : 0 ≤ Real.log (V + 9) := Real.log_nonneg (by linarith)
  have hlog : Real.log (V + 9) ≤ Real.log V + 9 := by
    calc
      _ ≤ Real.log (V * 10) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log V + Real.log 10 := Real.log_mul hV0.ne' (by norm_num)
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)]
  have hVpow : 1 ≤ V ^ (1 / 4 : ℝ) := Real.one_le_rpow hV (by positivity)
  have hpow : Real.log V ≤ V ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div hV0.le (by positivity)
  by_cases h : x ≤ V
  · have hlogV : Real.log (V + 9) ≤ 13 * V ^ (1 / 4 : ℝ) := by linarith
    have hsquare : (V ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt V := by
      rw [← Real.rpow_mul_natCast hV0.le, Real.sqrt_eq_rpow]
      norm_num
    calc
      _ ≤ Real.sqrt V * (13 * V ^ (1 / 4 : ℝ)) ^ 2 := by
        exact mul_le_mul (Real.sqrt_le_sqrt h) (pow_le_pow_left₀ hlognonneg hlogV 2)
          (by positivity) (Real.sqrt_nonneg _)
      _ = 169 * V := by rw [mul_pow, hsquare]; nlinarith [Real.sq_sqrt hV0.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by norm_num)
  · have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hlogx : Real.log (V + 9) ≤ 9 * (1 + Real.log x) := by
      have hm := Real.log_le_log hV0 (le_of_not_ge h)
      linarith [Real.log_nonneg hx]
    calc
      _ ≤ Real.sqrt x * (9 * (1 + Real.log x)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlognonneg hlogx 2) (Real.sqrt_nonneg _)
      _ = 81 * (Real.sqrt x * (1 + Real.log x)^2) := by ring
      _ ≤ _ := by nlinarith [show 0 ≤ Real.sqrt x * (1 + Real.log x)^2 by positivity]


/-- Reflection carries the right-half bound to the left half with an additive logarithmic term. -/
private theorem horizontal_reflection {V B : ℝ} (hRH : RiemannHypothesis)
    (hV : 2 ≤ |V|)
    (hgood : ∀ s : ℂ, (s.im = V ∨ s.im = -V) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ B)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (-1 / 4 : ℝ) 2) :
    riemannZeta ((σ : ℂ) + V * I) ≠ 0 ∧
      ‖logDeriv riemannZeta ((σ : ℂ) + V * I)‖ ≤ B + Real.log (|V| + 2) + 17 := by
  let s : ℂ := (σ : ℂ) + V * I
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = V := by simp [s]
  have h1s_re : (1 - s).re = 1 - σ := by simp [hs_re]
  have h1s_im : (1 - s).im = -V := by simp [hs_im]
  have hV₀ : V ≠ 0 := by
    intro hz
    norm_num [hz] at hV
  have hlog : 0 ≤ Real.log (|V| + 2) := Real.log_nonneg (by linarith [abs_nonneg V])
  change riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ _
  by_cases hr : 1 / 2 ≤ σ
  · obtain ⟨hz, hn⟩ := hgood s (Or.inl hs_im) (by rwa [hs_re]) (by simpa [hs_re] using hσ.2)
    exact ⟨hz, hn.trans (by linarith)⟩
  have hs_int (n : ℤ) : s ≠ n := ofReal_add_mul_I_ne_intCast σ hV₀ n
  have hz : riemannZeta s ≠ 0 := by
    intro hz
    have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      have him := congrArg Complex.im hn
      exact hV₀ (by simpa [hs_im] using him)
    have hout := hRH s hz htriv (by simpa using hs_int 1)
    exact hr (le_of_eq (hs_re.symm.trans hout).symm)
  refine ⟨hz, ?_⟩
  have hrefl := (hgood (1 - s) (Or.inr h1s_im) (by rw [h1s_re]; linarith)
    (by rw [h1s_re]; linarith [hσ.1])).2
  have hlogp : ‖Complex.log (2 * π)‖ ≤ 7 := by
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [show (2 * π : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      ← ofReal_log hp.le, norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos (by linarith [Real.pi_gt_three]))]
    linarith [Real.log_le_sub_one_of_pos hp, Real.pi_lt_four]
  have hd : ‖digamma s‖ ≤ Real.log (|V| + 2) + 6 := by
    have hd := norm_digamma_horizontal_le (V := V) ⟨hσ.1, le_of_not_ge hr⟩ hV
    linarith [Real.pi_lt_four]
  have ht : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ 4 := by
    rw [norm_mul, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_ofNat]
    have ht := norm_tan_pi_mul_div_two_le_two σ hV
    calc
      _ ≤ Real.pi / 2 * 2 := mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ _ := by linarith [Real.pi_lt_four]
  rw [logDeriv_riemannZeta_one_sub hs_int hz]
  have h₁ := norm_add_le (-logDeriv riemannZeta (1 - s)) (Complex.log (2 * π))
  have h₂ := norm_sub_le (-logDeriv riemannZeta (1 - s) + Complex.log (2 * π)) (digamma s)
  have h₃ := norm_add_le (-logDeriv riemannZeta (1 - s) + Complex.log (2 * π) - digamma s)
    (π / 2 * Complex.tan (π * s / 2))
  rw [norm_neg] at h₁
  linarith

/-- A good height for the whole horizontal segment, with a square-logarithmic bound. -/
private theorem landau_good_heights (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 7 ≤ j →
      ∃ V : ℝ, (j : ℝ) ≤ V ∧ V ≤ (j : ℝ) + 1 ∧
        ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
          riemannZeta ((σ : ℂ) + V * I) ≠ 0 ∧
          ‖logDeriv riemannZeta ((σ : ℂ) + V * I)‖ ≤ C * Real.log ((j : ℝ) + 3) ^ 2 := by
  obtain ⟨C, hC, h⟩ := Zeta23.WeilEF.good_heights_at
  refine ⟨C + 18, by positivity, fun j hj => ?_⟩
  obtain ⟨V, hlo, hhi, hgood⟩ := h j hj
  have hj' : (7 : ℝ) ≤ j := by exact_mod_cast hj
  have hV : 2 ≤ V := by linarith
  have he : |V| = V := abs_of_nonneg (by linarith)
  have hL : 1 ≤ Real.log ((j : ℝ) + 3) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
  refine ⟨V, hlo, hhi, fun σ hσ => ?_⟩
  obtain ⟨hn, hnrm⟩ := horizontal_reflection hRH (by rwa [he]) hgood hσ
  refine ⟨hn, hnrm.trans ?_⟩
  rw [he]
  have hlog := Real.log_le_log (x := V + 2) (y := (j : ℝ) + 3) (by positivity)
    (by linarith)
  nlinarith

private theorem norm_horizontal_integral_at_good_height (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 7 ≤ j →
      ∃ V : ℝ, (j : ℝ) ≤ V ∧ V ≤ (j : ℝ) + 1 ∧
        (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2, riemannZeta ((σ : ℂ) + V * I) ≠ 0) ∧
        ∀ {x c : ℝ}, 1 < x → -1 / 4 ≤ c → c ≤ 2 →
          ‖∫ σ in (-1 / 4 : ℝ)..c, (x : ℂ) ^ ((σ : ℂ) + V * I) *
            (-logDeriv riemannZeta ((σ : ℂ) + V * I))‖ ≤
            C * (c + 1 / 4) * x ^ c * Real.log ((j : ℝ) + 3) ^ 2 := by
  obtain ⟨C, hC, h⟩ := landau_good_heights hRH
  refine ⟨C, hC, fun j hj => ?_⟩
  obtain ⟨V, hlo, hhi, hgood⟩ := h j hj
  refine ⟨V, hlo, hhi, fun σ hσ => (hgood σ hσ).1, ?_⟩
  intro x c hx hcl hch
  let f (σ : ℝ) := (x : ℂ) ^ ((σ : ℂ) + V * I) * (-logDeriv riemannZeta ((σ : ℂ) + V * I))
  have hf (σ) (hσ : σ ∈ Set.uIoc (-1 / 4 : ℝ) c) :
      ‖f σ‖ ≤ x ^ c * (C * Real.log ((j : ℝ) + 3) ^ 2) := by
    rw [Set.uIoc_of_le hcl] at hσ
    have hσ' : σ ∈ Set.Icc (-1 / 4 : ℝ) 2 := ⟨hσ.1.le, hσ.2.trans hch⟩
    dsimp only [f]
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
    simp only [add_re, ofReal_re, mul_I_re, neg_zero, add_zero, ofReal_im]
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx.le hσ.2) (hgood σ hσ').2
      (norm_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hx.le) _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hf
  rw [abs_of_nonneg (by linarith : 0 ≤ c - -1 / 4)] at hi
  convert hi using 1
  ring
private noncomputable def cutoffScore (rh : RiemannHypothesis) (V t : ℝ) : ℂ :=
  ∑ j ∈ positiveCutoff rh V, (zeroMult j.val : ℂ) * phase (ordinate j) t

private theorem cutoffScore_transfer (rh : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ {V U t : ℝ}, 1 ≤ V → V ≤ U → U ≤ V + 2 →
      ‖cutoffScore rh V t‖ ≤ ‖cutoffScore rh U t‖ + C * Real.log (V + 9) := by
  classical
  obtain ⟨A, hA, hlocal⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hLC := Zeta23.Tail.LocalCount.ofWindowCount zetaZeroConfig hA hlocal
  refine ⟨6 * A, by linarith, fun {V U t} hV hVU hUV => ?_⟩
  let a : ℤ := ⌊V⌋
  let E : PositiveZetaZero ↪ zetaZeroConfig.carrier :=
    ⟨fun j => ⟨j.val, j.property.1⟩, fun p q h => Subtype.ext (congrArg (fun z : zetaZeroConfig.carrier => (z : ℂ)) h)⟩
  let band := positiveCutoff rh U \ positiveCutoff rh V
  let F := band.map E
  have hlo : (a : ℝ) ≤ V := Int.floor_le _
  have hhi : V < (a : ℝ) + 1 := Int.lt_floor_add_one _
  have ha : 0 ≤ (a : ℝ) := by linarith
  have hwindow (z : zetaZeroConfig.carrier) (hz : z ∈ F) :
      (a : ℝ) < (z : ℂ).im ∧ (z : ℂ).im ≤ (a : ℝ) + 6 := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hz
    have hm := Finset.mem_sdiff.mp hj
    have h₁ := (RHHarmonicPairMoment.cutoff_mem rh U j).mp hm.1
    have h₂ := mt (RHHarmonicPairMoment.cutoff_mem rh V j).mpr hm.2
    change (a : ℝ) < ordinate j ∧ ordinate j ≤ (a : ℝ) + 6
    exact ⟨hlo.trans_lt (lt_of_not_ge h₂), by linarith⟩
  have hmass : (∑ j ∈ band, (zeroMult j.val : ℝ)) ≤ 6 * A * Real.log (V + 9) := by
    have h := Zeta23.WeilEF.sum_mult_six_windows hLC F hwindow
    dsimp only [F] at h
    rw [Finset.sum_map, abs_of_nonneg ha] at h
    change (∑ j ∈ band, (zeroMult j.val : ℝ)) ≤ _ at h
    refine h.trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) (by positivity)
  let g (j : PositiveZetaZero) : ℂ := (zeroMult j.val : ℂ) * phase (ordinate j) t
  have hsplit : ∑ j ∈ band, g j = cutoffScore rh U t - cutoffScore rh V t :=
    eq_sub_of_add_eq (Finset.sum_sdiff (RHHarmonicPairMoment.cutoff_mono rh hVU))
  have hband : ‖∑ j ∈ band, g j‖ ≤ 6 * A * Real.log (V + 9) := by
    refine (norm_sum_le _ _).trans ?_
    simpa [g, norm_mul, norm_phase, Complex.norm_natCast] using hmass
  have he : cutoffScore rh V t = cutoffScore rh U t - ∑ j ∈ band, g j := by rw [hsplit]; abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add_right hband _)

private theorem norm_cutoffScore_neg (rh : RiemannHypothesis) (V t : ℝ) :
    ‖cutoffScore rh V (-t)‖ = ‖cutoffScore rh V t‖ := by
  have hp (v : ℝ) : phase v (-t) = (starRingEnd ℂ) (phase v t) := by
    unfold phase
    rw [← exp_conj]
    congr 1
    simp only [map_mul, conj_ofReal, conj_I, ofReal_neg]
    ring
  have h : cutoffScore rh V (-t) = (starRingEnd ℂ) (cutoffScore rh V t) := by
    unfold cutoffScore
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, Complex.conj_natCast, hp]
  rw [h, Complex.norm_conj]

private theorem zeta_cutoff_power_eq (rh : RiemannHypothesis) {x V : ℝ} (hx : 0 < x) :
    ∑ j ∈ positiveCutoff rh V, (zeroMult j.val : ℂ) * (x : ℂ) ^ j.val =
      (Real.sqrt x : ℂ) * cutoffScore rh V (Real.log x) := by
  have hid (j : PositiveZetaZero) : (x : ℂ) ^ j.val =
      (Real.sqrt x : ℂ) * phase (ordinate j) (Real.log x) := by
    have hr := rh_re_eq_half rh j.property.2 j.property.1.1
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← ofReal_log hx.le]
    have he : (Real.log x : ℂ) * j.val =
        ((Real.log x * (1 / 2) : ℝ) : ℂ) + (ordinate j : ℂ) * I * (Real.log x : ℂ) := by
      rw [show j.val = (j.val.re : ℂ) + j.val.im * I from (re_add_im j.val).symm, hr]
      change _ = _ + (j.val.im : ℂ) * I * _
      push_cast
      ring
    rw [he, exp_add, ← ofReal_exp, ← Real.rpow_def_of_pos hx, ← Real.sqrt_eq_rpow, phase]
  simp only [cutoffScore, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hid]
  ring

private theorem norm_rect_integral_le_edges (g : ℂ → ℂ) (c V : ℝ) :
    ‖RectangleIntegral' g ((-1 / 4 : ℂ) + I) ((c : ℂ) + V * I)‖ ≤
      ‖∫ σ in (-1 / 4 : ℝ)..c, g ((σ : ℂ) + I)‖ +
      ‖∫ σ in (-1 / 4 : ℝ)..c, g ((σ : ℂ) + V * I)‖ +
      ‖∫ t in (1 : ℝ)..V, g ((c : ℂ) + t * I)‖ +
      ‖∫ t in (1 : ℝ)..V, g ((-1 / 4 : ℂ) + t * I)‖ := by
  have hzre : ((-1 / 4 : ℂ) + I).re = -1 / 4 := by norm_num
  have hzim : ((-1 / 4 : ℂ) + I).im = 1 := by norm_num
  have hwre : ((c : ℂ) + V * I).re = c := by simp
  have hwim : ((c : ℂ) + V * I).im = V := by simp
  unfold RectangleIntegral' RectangleIntegral HIntegral VIntegral
  simp only [hzre, hzim, hwre, hwim, ofReal_one, one_mul]
  push_cast
  have hnorm : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, norm_ofNat, norm_I, mul_one,
      norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  rw [norm_smul]
  refine (mul_le_of_le_one_left (norm_nonneg _) hnorm).trans ?_
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
    rw [norm_smul, norm_I, one_mul]
  · rw [norm_smul, norm_I, one_mul]

private theorem cutoff_empty_of_le_six (rh : RiemannHypothesis) {V : ℝ} (hsmall : V ≤ 6) :
    positiveCutoff rh V = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have he := (RHHarmonicPairMoment.cutoff_mem rh V j).mp hj
  change j.val.im ≤ V at he
  linarith [six_lt_height rh j.property.2 j.property.1.1]


set_option maxHeartbeats 800000 in
/-- Combine the rectangle estimates at a nearby zero-free height and transfer the sum. -/
private theorem landau_positive_frequency (rh : RiemannHypothesis) :
    ∃ D : ℝ, 0 < D ∧ ∀ {V x : ℝ}, 1 < V → 1 < x →
      ‖cutoffScore rh V (Real.log x)‖ ≤ D *
        (V + Real.sqrt x * (1 + Real.log x)^2 + (1 + Real.log V) / Real.log x) := by
  obtain ⟨A, hA, htop⟩ := norm_horizontal_integral_at_good_height rh
  obtain ⟨B, hB, hbottom⟩ := norm_integral_landau_bottom rh
  obtain ⟨C, hC, htransfer⟩ := cutoffScore_transfer rh
  refine ⟨10000 * (A+B+C+1), by positivity, fun {V x} hV hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hg : 0 < Real.log x := Real.log_pos hx
  have hVlog : 0 ≤ Real.log V := Real.log_nonneg hV.le
  let W := Real.sqrt x
  let M := W * (1 + Real.log x)^2
  let N := (1 + Real.log V) / Real.log x
  have hW : 0 < W := Real.sqrt_pos_of_pos hx0
  have hW1 : 1 ≤ W := by simpa [W] using Real.sqrt_le_sqrt hx.le
  have hWsq : W * W = x := Real.mul_self_sqrt hx0.le
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  by_cases hsmall : V ≤ 6
  · have hempty : positiveCutoff rh V = ∅ := by
      exact cutoff_empty_of_le_six rh hsmall
    simp only [cutoffScore, hempty, Finset.sum_empty, norm_zero]
    positivity
  let j : ℕ := ⌈V⌉₊
  have hjlo : V ≤ (j : ℝ) := Nat.le_ceil _
  have hjhi : (j : ℝ) < V + 1 := Nat.ceil_lt_add_one (by linarith)
  have hj : 7 ≤ j := by
    have he : (6 : ℕ) < j := by exact_mod_cast (show (6 : ℝ) < j by linarith)
    omega
  obtain ⟨U, hUj, hjU, hno, htopU⟩ := htop j hj
  have hVU : V ≤ U := hjlo.trans hUj
  have hUV : U ≤ V + 2 := by linarith
  have hU1 : 1 < U := hV.trans_le hVU
  let c := 1 + (Real.log (3 * x))⁻¹
  obtain ⟨hc, hc₂, hcx, _, _⟩ := LandauRightVertical.movingLineBounds hx
  change 1 < c at hc
  change c ≤ 2 at hc₂
  change x ^ c ≤ 3*x at hcx
  have hc₀ : (-1 / 4 : ℝ) ≤ c := by linarith
  let f (s : ℂ) := (x : ℂ) ^ s * logDeriv riemannZeta s
  have hid := landau_rectangle_eq_actual_cutoff rh hx hc hU1.le
    (fun σ hσ => hno σ ⟨hσ.1, hσ.2.trans hc₂⟩)
  rw [zeta_cutoff_power_eq rh hx0] at hid
  change RectangleIntegral' f ((-1 / 4 : ℂ) + I) ((c : ℂ) + U * I) =
    (W : ℂ) * cutoffScore rh U (Real.log x) at hid
  have hn := norm_rect_integral_le_edges f c U
  rw [hid, norm_mul, norm_real, Real.norm_of_nonneg hW.le] at hn
  have hneg (s : ℂ) : f s = -((x : ℂ) ^ s * (-logDeriv riemannZeta s)) := by simp [f]
  simp_rw [hneg, intervalIntegral.integral_neg, norm_neg] at hn
  have htopn := htopU hx hc₀ hc₂
  have hbotn := hbottom hx hc₀ hc₂
  have hright := D5.S3.Weil.ZetaExplicit.LandauRightVertical.norm_right_vertical_integral hx hU1
  change ‖∫ t in 1..U, (x : ℂ) ^ ((c : ℂ) + t * I) *
      (- deriv riemannZeta ((c : ℂ) + t * I) / riemannZeta ((c : ℂ) + t * I))‖ ≤ _ at hright
  simp only [neg_div, ← logDeriv_apply] at hright
  have hleft := D5.S3.Weil.ZetaExplicit.LandauLeftVertical.norm_left_vertical_integral hx hU1.le
  have hU3 : U ≤ 3*V := by linarith
  have hlU : Real.log U ≤ Real.log V + 2 := by
    calc
      _ ≤ Real.log (3*V) := Real.log_le_log (by linarith) hU3
      _ = Real.log V + Real.log 3 := by rw [Real.log_mul (by norm_num) (by linarith : V ≠ 0), add_comm]
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hln2 : 0 ≤ Real.log (2*x) := Real.log_nonneg (by linarith)
  have hln2add : Real.log (2*x) ≤ 1 + Real.log x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hln2W : Real.log (2*x) ≤ 3*W := by
    have hh := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at hh
    change Real.log x ≤ W / (1 / 2) at hh
    linarith
  have hR : 400 * (U * Real.log (2*x) + x * Real.log (2*x)^2) ≤ W * (3600 * V + 400 * M) := by
    have h₁ : U * Real.log (2*x) ≤ (3*V)*(3*W) :=
      mul_le_mul hU3 hln2W hln2 (by positivity)
    have h₂ : x * Real.log (2*x)^2 ≤ x * (1 + Real.log x)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hln2 hln2add 2) hx0.le
    dsimp only [M]
    calc
      _ ≤ 400 * ((3*V)*(3*W) + x * (1 + Real.log x)^2) :=
        mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by norm_num)
      _ = _ := by rw [← hWsq]; ring
  have hL : x ^ (-1 / 4 : ℝ) * (80 * (U - 1) + 20 * (1 + Real.log U) / Real.log x) ≤
      W * (240 * V + 60 * N) := by
    have hxinv : x ^ (-1 / 4 : ℝ) ≤ 1 := by
      simpa using (Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num : (-1 / 4 : ℝ) ≤ 0))
    have h₁ : (1 + Real.log U) / Real.log x ≤ 3*N := by
      dsimp only [N]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith) hg.le
    have h₂ : 80 * (U - 1) + 20 * (1 + Real.log U) / Real.log x ≤ 240 * V + 60 * N := by
      rw [mul_div_assoc]
      nlinarith only [hU3, h₁]
    exact mul_le_mul (hxinv.trans hW1) h₂
      (by have := Real.log_nonneg hU1.le; positivity) hW.le
  have hwidth : c + 1 / 4 ≤ 9 / 4 := by linarith
  have hgeom : (c + 1 / 4) * x ^ c ≤ 7 * x := by
    have h := mul_le_mul hwidth hcx (Real.rpow_nonneg hx0.le _)
      (by norm_num : (0:ℝ) ≤ 9 / 4)
    linarith
  have hbot : B * (c + 1 / 4) * x ^ c ≤ W * (7 * B * M) := by
    have h := mul_le_mul_of_nonneg_left hgeom hB.le
    have hsq : (1 + Real.log x)^2 ≥ 1 := by nlinarith
    have hs : W ≤ M := by
      dsimp only [M]
      simpa using (mul_le_mul_of_nonneg_left hsq hW.le)
    have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ 7 * B * W by positivity)
    rw [← hWsq] at h
    nlinarith
  have htop' : A * (c + 1 / 4) * x ^ c * Real.log ((j : ℝ) + 3)^2 ≤
      W * (1183 * A * (V + M)) := by
    have hlog : Real.log ((j : ℝ) + 3) ≤ Real.log (V+9) :=
      Real.log_le_log (by positivity) (by linarith)
    have hj0 : 0 ≤ Real.log ((j : ℝ) + 3) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j])
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hgeom hA.le)
      (pow_le_pow_left₀ hj0 hlog 2) (sq_nonneg _) (mul_nonneg hA.le (mul_nonneg (by norm_num) hx0.le))
    have ha := mul_le_mul_of_nonneg_left (sqrt_mul_square_log_absorb hx.le hV.le)
      (show 0 ≤ W * (7 * A) from mul_nonneg hW.le (mul_nonneg (by norm_num) hA.le))
    change W * (7*A) * (W * Real.log (V+9)^2) ≤ W * (7*A) * (169 * (V+M)) at ha
    calc
      _ ≤ A * (7*x) * Real.log (V+9)^2 := by simpa only [mul_assoc] using hh
      _ = W * (7*A) * (W * Real.log (V+9)^2) := by rw [← hWsq]; ring
      _ ≤ W * (7*A) * (169*(V+M)) := ha
      _ = _ := by ring
  have hUn : ‖cutoffScore rh U (Real.log x)‖ ≤
      7 * B * M + 1183 * A * (V + M) + (3600 * V + 400 * M) + (240 * V + 60 * N) := by
    apply le_of_mul_le_mul_left _ hW
    have e₁ := hbotn.trans hbot
    have e₂ := htopn.trans htop'
    have e₃ := hright.trans hR
    have e₄ := hleft.trans hL
    refine hn.trans ?_
    calc
      _ ≤ W * (7 * B * M) + W * (1183 * A * (V + M)) +
          W * (3600 * V + 400 * M) + W * (240 * V + 60 * N) :=
        add_le_add (add_le_add (add_le_add e₁ e₂) e₃) e₄
      _ = _ := by ring
  have htrans := htransfer (t := Real.log x) hV.le hVU hUV
  have hlogV9 : Real.log (V+9) ≤ 9*V := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < V+9 by positivity)]
  have hcnt := mul_le_mul_of_nonneg_left hlogV9 hC.le
  change ‖cutoffScore rh V (Real.log x)‖ ≤ 10000 * (A+B+C+1) * (V+M+N)
  have hbudget : 7*B*M + 1183*A*(V+M) + (3600*V+400*M) + (240*V+60*N) + C*(9*V) ≤
      10000*(A+B+C+1)*(V+M+N) := by
    have ha : 0 ≤ A*(V+M) := by positivity
    nlinarith [mul_nonneg hA.le hN, mul_nonneg hB.le (by linarith : 0 ≤ V),
      mul_nonneg hB.le hN, mul_nonneg hC.le (by linarith : 0 ≤ V), mul_nonneg hC.le hM,
      mul_nonneg hC.le hN, mul_nonneg hB.le hM]
  linarith

/-- A uniform Landau bound for the inclusive phase sum of positive zeta ordinates. -/
theorem actual_cutoff_landau_envelope (rh : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ V t : ℝ, 1 < V → 0 < |t| →
      ‖∑ j ∈ positiveCutoff rh V, (zeroMult j.val : ℂ) * phase (ordinate j) t‖ ≤
        let expFrequency := Real.exp
        C * (V + expFrequency (|t| / 2) * (1 + |t|)^2 + Real.log V / |t|) := by
  obtain ⟨C, hC, h⟩ := landau_positive_frequency rh
  refine ⟨2 * C, by positivity, fun V t hV ht => ?_⟩
  by_cases hsmall : V ≤ 6
  · rw [cutoff_empty_of_le_six rh hsmall, Finset.sum_empty, norm_zero]
    have := Real.log_nonneg hV.le
    positivity
  have hp := h (x := Real.exp |t|) hV (Real.one_lt_exp_iff.mpr ht)
  rw [Real.log_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at hp
  rw [show |t| * (1 / 2 : ℝ) = |t| / 2 by ring] at hp
  have he : ‖cutoffScore rh V t‖ = ‖cutoffScore rh V |t|‖ := by
    by_cases hs : 0 ≤ t
    · rw [abs_of_nonneg hs]
    · rw [abs_of_neg (lt_of_not_ge hs), norm_cutoffScore_neg]
  change ‖cutoffScore rh V t‖ ≤ _
  rw [he]
  refine hp.trans ?_
  have hlog : 1 ≤ Real.log V := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
  have hdiv : (1 + Real.log V) / |t| ≤ 2 * (Real.log V / |t|) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) ht.le
  have hterm : 0 ≤ Real.exp (|t| / 2) * (1 + |t|)^2 := by positivity
  nlinarith only [mul_nonneg hC.le (zero_le_one.trans hV.le), mul_nonneg hC.le hterm,
    mul_le_mul_of_nonneg_left hdiv hC.le]

end D5.S3.Weil.ZetaExplicit.LandauUniformCutoff
