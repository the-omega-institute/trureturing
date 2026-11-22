/- GID: D5/S3/Weil/ZetaPntBounds/MobiusShortAverage
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/MobiusShortAverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative short Riesz averages for the ordinary Möbius prefix. -/

import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes.Integral
import D5.S3.Weil.Mertens.LittlewoodUpstream.ZetaReciprocalSubpolynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! Short secants of first Riesz sums recover ordinary signed prefixes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaPntBounds.MobiusShortAverage

open Complex Set MeasureTheory ArithmeticFunction Filter
open scoped Topology
open scoped ArithmeticFunction.Moebius
open ConjectureMachines.Semantics.Riemann.WeightedStieltjes

private def shortKernel (x h : ℝ) (s : ℂ) : ℂ :=
  (smoothedPerronKernel (x+h) s - smoothedPerronKernel x s) / (h : ℂ)

private theorem norm_shortKernel_le_first {x h : ℝ} {s : ℂ}
    (hx : 0 < x) (hh : 0 < h) (hs : 0 < s.re) :
    ‖shortKernel x h s‖ ≤ (x+h)^s.re / ‖s‖ := by
  have hs₀ : s ≠ 0 := by
    intro he
    simp [he] at hs
  have hs₁ : s ≠ -1 := by
    intro he
    norm_num [he] at hs
  let F (y : ℝ) := (y : ℂ)^(s+1)/(s+1)
  have hderiv (y : ℝ) (hy : y ∈ Icc x (x+h)) :
      HasDerivWithinAt F ((y : ℂ)^s) (Icc x (x+h)) y :=
    (hasDerivAt_ofReal_cpow_const' (hx.trans_le hy.1).ne' hs₁).hasDerivWithinAt
  have hb (y : ℝ) (hy : y ∈ Icc x (x+h)) :
      ‖(y : ℂ)^s‖ ≤ (x+h)^s.re := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans_le hy.1)]
    exact Real.rpow_le_rpow (hx.trans_le hy.1).le hy.2 hs.le
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hb
    (convex_Icc x (x+h)) (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
  have hnorm : ‖F (x+h) - F x‖ ≤ (x+h)^s.re * h := by
    simpa only [add_sub_cancel_left, Real.norm_of_nonneg hh.le] using hbound
  have hrewrite : shortKernel x h s = (F (x+h)-F x)/(s*(h : ℂ)) := by
    have hs₁' : s+1 ≠ 0 := by
      intro hz
      apply hs₁
      linear_combination hz
    have hh' : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
    unfold shortKernel smoothedPerronKernel F
    field_simp
  rw [hrewrite, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh.le]
  exact (div_le_div_of_nonneg_right hnorm (by positivity)).trans_eq
    (by field_simp)

private theorem norm_shortKernel_le_second {x h : ℝ} {s : ℂ}
    (hx : 0 < x) (hh : 0 < h) (hs : 0 < s.re) :
    ‖shortKernel x h s‖ ≤ 2 * (x+h)^(s.re+1) / (h * (‖s‖ * ‖s+1‖)) := by
  have hx' : 0 < x+h := by positivity
  have htime : x^(s.re+1) ≤ (x+h)^(s.re+1) :=
    Real.rpow_le_rpow hx.le (by linarith) (by linarith)
  have hsub := norm_sub_le (smoothedPerronKernel (x+h) s) (smoothedPerronKernel x s)
  unfold shortKernel
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hh.le]
  refine (div_le_div_of_nonneg_right hsub hh.le).trans ?_
  simp only [smoothedPerronKernel, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_cpow_eq_rpow_re_of_pos hx',
    Complex.add_re, Complex.one_re]
  rw [← add_div, div_div, mul_comm (_ * _) h]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith


private def rieszMean (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n * (x - n)

private theorem short_riesz_prefix_error {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1)
    (N : ℕ) {h : ℝ} (hh : 0 < h) :
    |(rieszMean a (N+h) - rieszMean a N)/h - ∑ n ∈ Finset.Ioc 0 N, a n| ≤ h := by
  let M := ⌊(N : ℝ)+h⌋₊
  let f (n : ℕ) := a n * ((N : ℝ)+h-n)
  have hNh : 0 ≤ (N : ℝ)+h := by positivity
  have hNM : N ≤ M := (Nat.le_floor_iff hNh).mpr (by linarith)
  have hf : (M : ℝ) ≤ (N : ℝ)+h := Nat.floor_le hNh
  have hrewrite :
      rieszMean a (N+h) - rieszMean a N =
        h * (∑ n ∈ Finset.Ioc 0 N, a n) + ∑ n ∈ Finset.Ioc N M, f n := by
    unfold rieszMean
    rw [Nat.floor_natCast, ← Finset.sum_Ioc_consecutive f (Nat.zero_le N) hNM]
    have heq : (∑ n ∈ Finset.Ioc 0 N, f n) -
        (∑ n ∈ Finset.Ioc 0 N, a n * ((N : ℝ)-n)) =
        h * (∑ n ∈ Finset.Ioc 0 N, a n) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by dsimp [f]; ring)
    linarith only [heq]
  have herror : |∑ n ∈ Finset.Ioc N M, f n| ≤ (M-N : ℕ) * h := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _ ∈ Finset.Ioc N M, h := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hnN, hnM⟩ := Finset.mem_Ioc.mp hn
        have hn₀ : (n : ℝ) ≤ (N : ℝ)+h :=
          (show (n : ℝ) ≤ M by exact_mod_cast hnM).trans hf
        have hn₁ : (N : ℝ) ≤ n := by exact_mod_cast hnN.le
        simp only [f, abs_mul, abs_of_nonneg (sub_nonneg.mpr hn₀)]
        exact mul_le_of_le_one_left (sub_nonneg.mpr hn₀) (ha n) |>.trans (by linarith)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
  rw [hrewrite]
  have heq : (h * (∑ n ∈ Finset.Ioc 0 N, a n) + ∑ n ∈ Finset.Ioc N M, f n) / h -
      (∑ n ∈ Finset.Ioc 0 N, a n) = (∑ n ∈ Finset.Ioc N M, f n) / h := by
    rw [add_div, mul_div_cancel_left₀ _ hh.ne']
    ring
  rw [heq, abs_div, abs_of_pos hh]
  have hn : ((M-N : ℕ) : ℝ) ≤ h := by rw [Nat.cast_sub hNM]; linarith
  exact (div_le_iff₀ hh).2 (herror.trans (mul_le_mul_of_nonneg_right hn hh.le))


private theorem height_le_norm {s : ℂ} (hs : 1/2 ≤ s.re) :
    1 + |s.im| ≤ 3 * ‖s‖ := by
  linarith only [Complex.abs_im_le_norm s, Complex.re_le_norm s, hs]

private theorem norm_reciprocal_shortKernel {x h C δ : ℝ} {s : ℂ}
    (hx : 0 < x) (hh : 0 < h) (hs : 1/2 ≤ s.re)
    (hC : 0 ≤ C) (hInv : ‖zetaInv s‖ ≤ C*(1+|s.im|)^δ) :
    ‖zetaInv s * shortKernel x h s‖ ≤ 3*C*(x+h)^s.re*(1+|s.im|)^(δ-1) ∧
      ‖zetaInv s * shortKernel x h s‖ ≤
        18*C*((x+h)^(s.re+1)/h)*(1+|s.im|)^(δ-2) := by
  let T := (1+|s.im|)
  have hT : 0 < T := by dsimp [T]; positivity
  have hs₀ : 0 < s.re := by linarith
  have hs₁ : 1/2 ≤ (s+1).re := by simpa only [add_re, one_re] using (show 1/2 ≤ s.re+1 by linarith)
  have hn₁ : 0 < ‖s‖ := by linarith only [hT, height_le_norm hs]
  have him : (s+1).im = s.im := by simp
  have h₂ : T ≤ 3*‖s+1‖ := by
    simpa only [T, him] using height_le_norm hs₁
  have hn₂ : 0 < ‖s+1‖ := by linarith only [hT, h₂]
  have hA : 1/‖s‖ ≤ 3/T := by
    exact (div_le_div_iff₀ hn₁ hT).2 (by simpa using height_le_norm hs)
  have hB : 1/‖s+1‖ ≤ 3/T := by
    exact (div_le_div_iff₀ hn₂ hT).2 (by simpa using h₂)
  constructor
  · calc
      _ ≤ (C*T^δ)*((x+h)^s.re/‖s‖) := by
        rw [norm_mul]
        exact mul_le_mul hInv (norm_shortKernel_le_first hx hh hs₀) (norm_nonneg _) (by positivity)
      _ ≤ (C*T^δ)*((x+h)^s.re*(3/T)) := by
        rw [div_eq_mul_one_div]
        gcongr
      _ = _ := by
        rw [sub_eq_add_neg, Real.rpow_add hT, Real.rpow_neg_one]
        dsimp only [T]
        ring
  · have hden : 1/(‖s‖*‖s+1‖) ≤ (3/T)*(3/T) := by
      rw [← one_div_mul_one_div]
      exact mul_le_mul hA hB (by positivity) (by positivity)
    calc
      _ ≤ (C*T^δ)*(2*(x+h)^(s.re+1)/(h*(‖s‖*‖s+1‖))) := by
        rw [norm_mul]
        exact mul_le_mul hInv (norm_shortKernel_le_second hx hh hs₀) (norm_nonneg _) (by positivity)
      _ ≤ (C*T^δ)*(2*((x+h)^(s.re+1)/h)*((3/T)*(3/T))) := by
        rw [← div_div, div_eq_mul_one_div (2*(x+h)^(s.re+1)/h), mul_div_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hden (by positivity)) (by positivity)
      _ = _ := by
        rw [sub_eq_add_neg, Real.rpow_add hT,
          show (-2 : ℝ) = -(2 : ℝ) by ring, Real.rpow_neg hT.le, Real.rpow_two]
        field_simp
        ring


private theorem norm_reciprocal_shortKernel_integrable_majorant {x h C δ : ℝ} {s : ℂ}
    (hx : 0 < x) (hh : 0 < h) (hs : 1/2 ≤ s.re)
    (hδ : 0 < δ) (hδ₁ : 2*δ ≤ 1)
    (hC : 0 ≤ C) (hInv : ‖zetaInv s‖ ≤ C*(1+|s.im|)^δ) :
    ‖zetaInv s * shortKernel x h s‖ ≤
      18*C*(x+h)^s.re*((x+h)/h)^(2*δ)*(1+|s.im|)^(-1-δ) := by
  let w := 1+|s.im|
  let Y := (x+h)/h
  let A := 18*C*(x+h)^s.re
  have hw : 0 < w := by dsimp [w]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbase : 0 ≤ A*w^(δ-1) := by positivity
  obtain ⟨hL, hH⟩ := norm_reciprocal_shortKernel hx hh hs hC hInv
  have ha : ‖zetaInv s * shortKernel x h s‖ ≤ A*w^(δ-1) := by
    refine hL.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    dsimp only [A]
    gcongr
    norm_num
  have hb : ‖zetaInv s * shortKernel x h s‖ ≤ (A*w^(δ-1))*(Y/w) := by
    refine hH.trans_eq ?_
    dsimp only [A, w, Y]
    rw [Real.rpow_add (show 0 < x+h by positivity), Real.rpow_one, div_eq_mul_inv ((x+h)/h),
      ← Real.rpow_neg_one, ← mul_assoc]
    calc
      _ = 18*C*(x+h)^s.re * ((x+h)/h) * (1+|s.im|)^(δ-2) := by ring
      _ = _ := by
        rw [show δ-2 = δ-1+(-1) by ring, Real.rpow_add (by positivity : 0 < 1+|s.im|)]
        ring
  have hv : ‖zetaInv s * shortKernel x h s‖ ≤ (A*w^(δ-1))*(Y/w)^(2*δ) := by
    by_cases hsmall : Y/w ≤ 1
    · exact hb.trans (mul_le_mul_of_nonneg_left
        (Real.self_le_rpow_of_le_one (by positivity) hsmall hδ₁) hbase)
    · exact ha.trans ((mul_one _).symm.le.trans
        (mul_le_mul_of_nonneg_left
          (Real.one_le_rpow (le_of_not_ge hsmall) (by positivity)) hbase))
  refine hv.trans_eq ?_
  rw [Real.div_rpow hY.le hw.le, div_eq_mul_inv, ← Real.rpow_neg hw.le]
  change A*w^(δ-1)*(Y^(2*δ)*w^(-(2*δ))) = A*Y^(2*δ)*w^(-1-δ)
  rw [show A*w^(δ-1)*(Y^(2*δ)*w^(-(2*δ))) =
    A*Y^(2*δ)*(w^(δ-1)*w^(-(2*δ))) by ring, ← Real.rpow_add hw]
  congr 2
  ring


private theorem shortKernel_differentiable {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    DifferentiableOn ℂ (shortKernel x h) {s : ℂ | θ < s.re} := by
  intro s hs
  have hre : 0 < s.re := hθ.trans_lt hs
  have h₀ : s ≠ 0 := by
    intro he
    simp [he] at hre
  have h₁ : s+1 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp only [add_re, one_re, zero_re] at h
    linarith
  have hopen : IsOpen {s : ℂ | s ≠ 0 ∧ s+1 ≠ 0} :=
    (isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_ne_fun (continuous_id.add continuous_const) continuous_const)
  exact (((differentiableOn_smoothedPerronKernel (by positivity : 0 < x+h) s ⟨h₀,h₁⟩).differentiableAt
    (hopen.mem_nhds ⟨h₀,h₁⟩)).sub
      ((differentiableOn_smoothedPerronKernel hx s ⟨h₀,h₁⟩).differentiableAt
        (hopen.mem_nhds ⟨h₀,h₁⟩))).div_const _ |>.differentiableWithinAt

private theorem shortKernel_vertical_shift {θ σ δ C x h : ℝ}
    (hθ : 1/2 ≤ θ) (hσ : θ < σ) (hσ₂ : σ ≤ 2)
    (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0)
    (hδ : 0 < δ) (hδ₁ : 2*δ ≤ 1) (hC : 0 ≤ C)
    (hInv : ∀ s : ℂ, σ ≤ s.re → ‖zetaInv s‖ ≤ C*(1+|s.im|)^δ)
    (hx : 1 ≤ x) (hh : 0 < h) :
    let F (s : ℂ) := zetaInv s * shortKernel x h s
    (∫ t : ℝ, F (σ + (t : ℂ)*I)) = ∫ t : ℝ, F (2 + (t : ℂ)*I) := by
  let F (s : ℂ) := zetaInv s * shortKernel x h s
  let U := {s : ℂ | θ < s.re}
  let point (c t : ℝ) := (c : ℂ)+(t : ℂ)*I
  let Y := (x+h)/h
  have hx₀ := zero_lt_one.trans_le hx
  have hxh : 1 ≤ x+h := by linarith
  have hre (c t : ℝ) : (point c t).re = c := by
    simp [point, Complex.add_re, Complex.mul_re]
  have him (c t : ℝ) : (point c t).im = t := by
    simp [point, Complex.add_im, Complex.mul_im]
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : DifferentiableOn ℂ F U :=
    (differentiableOn_zetaInv_of_zero_free hzero).mul
      (shortKernel_differentiable hx₀ hh (by linarith))
  have hmem (c : ℝ) (hc : σ ≤ c) (t : ℝ) : point c t ∈ U := by
    change θ < (point c t).re
    rw [hre]
    exact hσ.trans_le hc
  have hbound (c : ℝ) (hc : σ ≤ c) (t : ℝ) :
      ‖F (point c t)‖ ≤ 18*C*(x+h)^c*Y^(2*δ)*(1+|t|)^(-1-δ) := by
    have h : σ ≤ (point c t).re := by rwa [hre]
    have hs : (1/2 : ℝ) ≤ (point c t).re := hθ.trans (hσ.le.trans h)
    simpa only [F, hre, him, Y] using
      norm_reciprocal_shortKernel_integrable_majorant hx₀ hh hs hδ hδ₁ hC (hInv _ h)
  have hW : Integrable (fun t : ℝ => (1+|t|)^(-1-δ)) := by
    have hfin : (Module.finrank ℝ ℝ : ℝ) < 1+δ := by simpa using hδ
    have hw : Integrable (fun t : ℝ => (1+‖t‖)^(-(1+δ))) := integrable_one_add_norm hfin
    simpa [Real.norm_eq_abs, show -(1+δ) = -1-δ by ring] using hw
  have hi (c : ℝ) (hc : σ ≤ c) : Integrable (fun t : ℝ => F (point c t)) := by
    have hcont : Continuous (fun t : ℝ => F (point c t)) :=
      hF.continuousOn.comp_continuous (by dsimp [point]; fun_prop) (hmem c hc)
    exact (hW.const_mul _).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall (hbound c hc))
  let B (t : ℝ) := 18*C*(x+h)^(2 : ℝ)*Y^(2*δ)*(1+|t|)^(-1-δ)
  have hB : Tendsto B atTop (𝓝 0) := by
    have htail : Tendsto (fun t : ℝ => (1+|t|)^(-1-δ)) atTop (𝓝 0) := by
      have h₀ : Tendsto (fun t : ℝ => 1+|t|) atTop atTop :=
        tendsto_atTop_mono (fun t => by simpa only [id_eq] using (show t ≤ 1+|t| by linarith [le_abs_self t])) tendsto_id
      simpa [Function.comp_def, show -(1+δ) = -1-δ by ring] using
        (tendsto_rpow_neg_atTop (show 0 < 1+δ by positivity)).comp h₀
    simpa only [B, mul_zero] using tendsto_const_nhds.mul htail
  have hB₀ (t c : ℝ) (hc : c ∈ Set.uIcc σ 2) : ‖F (point c t)‖ ≤ B t := by
    have hc' : c ∈ Set.Icc σ 2 := by simpa only [Set.uIcc_of_le hσ₂] using hc
    refine (hbound c hc'.1 t).trans ?_
    dsimp only [B]
    gcongr
    · exact hc'.2
  change (∫ t : ℝ, F (point σ t)) = ∫ t : ℝ, F (point 2 t)
  have hcMem {c : ℝ} (hc : c ∈ Set.uIcc (2 : ℝ) σ) : c ∈ Set.Icc σ 2 := by
    simpa only [Set.uIcc_comm (2 : ℝ) σ, Set.uIcc_of_le hσ₂] using hc
  exact integral_vertical_eq_of_differentiableOn_strip hU hF
    (fun c hc t => hmem c (hcMem hc).1 t)
    (hi 2 hσ₂) (hi σ le_rfl) hB
    (Eventually.of_forall fun t c hc =>
      hB₀ t c (Set.uIcc_comm (2 : ℝ) σ ▸ hc))
    (Eventually.of_forall fun t c hc => by
      simpa only [B, abs_neg] using hB₀ (-t) c (Set.uIcc_comm (2 : ℝ) σ ▸ hc))



private theorem mobius_riesz_on_two {y : ℝ} (hy : 0 < y) :
    (rieszMean (fun n => (μ n : ℝ)) y : ℂ) =
      (2*(Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
        zetaInv (2+(t : ℂ)*I) * smoothedPerronKernel y (2+(t : ℂ)*I) := by
  let f (n : ℕ) : ℂ := (μ n : ℂ)
  have hsum : LSeriesSummable f (2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by norm_num)
  have he (t : ℝ) : LSeries f (2+(t : ℂ)*I) = zetaInv (2+(t : ℂ)*I) := by
    let s : ℂ := 2+(t : ℂ)*I
    have hs : 1 < s.re := by norm_num [s, add_re, mul_re]
    have hs₁ : s ≠ 1 := by
      intro h
      norm_num [h] at hs
    have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
    rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
    change riemannZeta s * LSeries f s = 1 at h
    rw [zetaInv, ite_eq_right hs₁, ← one_div]
    apply (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).2
    rw [mul_comm]
    exact h
  have h := smoothed_perron_LSeries hy (show (0 : ℝ) < 2 by norm_num) hsum
  have hset : Finset.Icc 1 ⌊y⌋₊ = Finset.Ioc 0 ⌊y⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  simp only [Complex.ofReal_ofNat, he, hset] at h
  simpa only [rieszMean, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_natCast, Complex.ofReal_intCast, f] using h

private theorem integrable_mobius_riesz_on_two {y : ℝ} (hy : 0 < y) :
    Integrable (fun t : ℝ => zetaInv (2+(t : ℂ)*I) *
      smoothedPerronKernel y (2+(t : ℂ)*I)) := by
  let s (t : ℝ) : ℂ := 2+(t : ℂ)*I
  have hs (t : ℝ) : (s t).re = 2 := by simp [s, add_re, mul_re]
  have hz (t : ℝ) : s t ≠ 1 := by
    intro e
    have h := hs t
    norm_num [e] at h
  have h0 (t : ℝ) : s t ≠ 0 := by
    intro e
    have h := hs t
    norm_num [e] at h
  have h1 (t : ℝ) : s t + 1 ≠ 0 := by
    intro e
    have h := congrArg Complex.re e
    rw [add_re, hs, one_re, zero_re] at h
    norm_num at h
  have hki : Integrable (fun t : ℝ => smoothedPerronKernel y (s t)) := by
    simpa only [s, Complex.ofReal_ofNat] using
      integrable_smoothedPerronKernel hy (show (0 : ℝ) < 2 by norm_num)
  have hcont : Continuous (fun t : ℝ => zetaInv (s t) * smoothedPerronKernel y (s t)) := by
    have hscont : Continuous s := by dsimp [s]; fun_prop
    have hζcont : Continuous (fun t : ℝ => riemannZeta (s t)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (differentiableAt_riemannZeta (hz t)).continuousAt.comp hscont.continuousAt
    have hζinv (t : ℝ) : zetaInv (s t) = (riemannZeta (s t))⁻¹ := by
      simp [zetaInv, hz t]
    simp_rw [hζinv]
    apply Continuous.mul
    · exact hζcont.inv₀ fun t => riemannZeta_ne_zero_of_one_lt_re (by rw [hs]; norm_num)
    · unfold smoothedPerronKernel
      exact ((differentiable_ofReal_cpow_add_one hy).continuous.comp hscont).div
        (hscont.mul (hscont.add continuous_const)) fun t => mul_ne_zero (h0 t) (h1 t)
  refine (hki.norm.const_mul (4 : ℝ)).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_zeta_lower_of_two_le_re (by rw [hs])).2.2 (norm_nonneg _)

private theorem mobius_short_riesz_on_two {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    (((rieszMean (fun n => (μ n : ℝ)) (x+h) -
      rieszMean (fun n => (μ n : ℝ)) x)/h : ℝ) : ℂ) =
      (2*(Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
        zetaInv (2+(t : ℂ)*I) * shortKernel x h (2+(t : ℂ)*I) := by
  let f (y t : ℝ) := zetaInv (2+(t : ℂ)*I) * smoothedPerronKernel y (2+(t : ℂ)*I)
  have hy : 0 < x+h := by positivity
  rw [Complex.ofReal_div, Complex.ofReal_sub, mobius_riesz_on_two hy, mobius_riesz_on_two hx]
  change ((2*(Real.pi : ℂ))⁻¹ * (∫ t, f (x+h) t) -
    (2*(Real.pi : ℂ))⁻¹ * (∫ t, f x t)) / (h : ℂ) = _
  rw [← mul_sub, ← integral_sub (integrable_mobius_riesz_on_two hy)
    (integrable_mobius_riesz_on_two hx), mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by dsimp [f, shortKernel]; ring


/-- A zero-free half-plane gives pointwise control of the ordinary Möbius prefix
up to every positive slack in the exponent. -/
theorem ordinary_mobius_prefix_of_zero_free {θ ε : ℝ}
    (hθ : 1/2 ≤ θ) (hθ₁ : θ < 1)
    (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0)
    (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, (μ n : ℝ)| ≤ D*(N : ℝ)^(θ+ε) := by
  let δ := min (ε/3) (1/4)
  let σ := θ+δ
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ₁ : 2*δ ≤ 1 := by linarith [min_le_right (ε/3) (1/4 : ℝ)]
  have hδε : 2*δ ≤ ε := by linarith [min_le_left (ε/3) (1/4 : ℝ)]
  have hσ : θ < σ := by dsimp [σ]; linarith
  have hσ₂ : σ ≤ 2 := by dsimp [σ]; linarith
  obtain ⟨C, hC, hInv⟩ := inv_zeta_isBigO_im_of_zero_free hθ hθ₁ hzero hσ hδ
  let w (t : ℝ) := (1+|t|)^(-1-δ)
  have hi : Integrable w := by
    have hfin : (Module.finrank ℝ ℝ : ℝ) < 1+δ := by simpa using hδ
    have hw : Integrable (fun t : ℝ => (1+‖t‖)^(-(1+δ))) := integrable_one_add_norm hfin
    simpa [w, Real.norm_eq_abs, show -(1+δ) = -1-δ by ring] using hw
  let W := ∫ t : ℝ, w t
  have hW : 0 ≤ W := integral_nonneg (fun t => by dsimp [w]; positivity)
  let k := ‖(2*(Real.pi : ℂ))⁻¹‖
  refine ⟨144*k*C*W+1, by positivity, fun N hN => ?_⟩
  let x := (N : ℝ)
  let h := Real.sqrt x
  let a (n : ℕ) := (μ n : ℝ)
  let F (t : ℝ) := zetaInv ((σ : ℂ)+(t : ℂ)*I) * shortKernel x h ((σ : ℂ)+(t : ℂ)*I)
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast hN
  have hx₀ := zero_lt_one.trans_le hx
  have hh : 0 < h := Real.sqrt_pos.2 hx₀
  have hsq : h*h = x := by dsimp [h]; nlinarith [Real.sq_sqrt hx₀.le]
  have hh₁ : 1 ≤ h := by dsimp [h]; simpa using Real.sqrt_le_sqrt hx
  have hhx : h ≤ x := by nlinarith only [hsq, mul_le_mul_of_nonneg_right hh₁ hh.le]
  have hy : x+h ≤ 2*x := by linarith
  have hyh : (x+h)/h ≤ 2*h := by
    apply (div_le_iff₀ hh).2
    nlinarith only [hy, hsq]
  have hmain : (((rieszMean a (x+h) - rieszMean a x)/h : ℝ) : ℂ) =
      (2*(Real.pi : ℂ))⁻¹ * ∫ t : ℝ, F t := by
    rw [mobius_short_riesz_on_two hx₀ hh,
      ← shortKernel_vertical_shift hθ hσ hσ₂ hzero hδ hδ₁ hC.le hInv hx hh]
  have hp : (x+h)^σ ≤ 4*x^σ := by
    refine (Real.rpow_le_rpow (by positivity) hy (by linarith)).trans ?_
    rw [Real.mul_rpow (by norm_num) hx₀.le]
    have htwo : (2 : ℝ)^σ ≤ 4 := by
      have he : (2 : ℝ)^(2 : ℝ) = 4 := by norm_num [Real.rpow_two]
      rw [← he]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ₂
    exact mul_le_mul_of_nonneg_right htwo (by positivity)
  have hpow : ((x+h)/h)^(2*δ) ≤ 2*x^δ := by
    refine (Real.rpow_le_rpow (by positivity) hyh (by positivity)).trans ?_
    rw [Real.mul_rpow (by norm_num) hh.le]
    have hhpow : h^(2*δ) = x^δ := by
      rw [show 2*δ = (2 : ℝ)*δ by rfl, Real.rpow_mul hh.le, Real.rpow_two, sq, hsq]
    rw [hhpow]
    have htwo : (2 : ℝ)^(2*δ) ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hδ₁
    exact mul_le_mul_of_nonneg_right htwo (by positivity)
  have hsumexp : σ+δ ≤ θ+ε := by dsimp [σ]; linarith
  have hsqrt_exp : (1/2 : ℝ) ≤ θ+ε := by linarith
  have hcoef : 18*C*(x+h)^σ*((x+h)/h)^(2*δ) ≤ 144*C*x^(θ+ε) := by
    calc
      _ ≤ (18*C*(4*x^σ))*(2*x^δ) := mul_le_mul
        (mul_le_mul_of_nonneg_left hp (by positivity)) hpow (by positivity) (by positivity)
      _ = (144*C)*(x^σ*x^δ) := by ring
      _ = (144*C)*x^(σ+δ) := by
        exact congrArg (fun v : ℝ => (144*C)*v) (Real.rpow_add hx₀ σ δ).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx hsumexp) (by positivity)
  have hbound (t : ℝ) : ‖F t‖ ≤ (144*C*x^(θ+ε))*w t := by
    let s := (σ : ℂ)+(t : ℂ)*I
    have hre : s.re = σ := by simp [s, add_re, mul_re]
    have him : s.im = t := by simp [s, add_im, mul_im]
    have hs : 1/2 ≤ s.re := by rw [hre]; exact hθ.trans hσ.le
    have hb := norm_reciprocal_shortKernel_integrable_majorant hx₀ hh hs hδ hδ₁
      hC.le (hInv s (by rw [hre]))
    exact (show ‖F t‖ ≤ _ from by simpa only [F, hre, him, w] using hb).trans
      (mul_le_mul_of_nonneg_right hcoef (by dsimp [w]; positivity))
  have hcont : Continuous F := by
    have hU : DifferentiableOn ℂ (fun s => zetaInv s * shortKernel x h s)
        {s : ℂ | θ < s.re} := (differentiableOn_zetaInv_of_zero_free hzero).mul
          (shortKernel_differentiable hx₀ hh (by linarith))
    exact hU.continuousOn.comp_continuous (by fun_prop)
      (fun t => by simpa [add_re, mul_re] using hσ)
  have hInt : Integrable F :=
    (hi.const_mul _).mono' hcont.aestronglyMeasurable (Eventually.of_forall hbound)
  have hm : |(rieszMean a (x+h) - rieszMean a x)/h| ≤
      (144*k*C*W)*x^(θ+ε) := by
    have h := congrArg norm hmain
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul] at h
    rw [h]
    refine (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm F) (norm_nonneg _)).trans ?_
    have hb := integral_mono hInt.norm (hi.const_mul (144*C*x^(θ+ε))) hbound
    rw [integral_const_mul] at hb
    exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq
      (by dsimp only [k, W]; ring)
  have herror := short_riesz_prefix_error (a := a)
    (fun n => by dsimp [a]; exact_mod_cast (abs_moebius_le_one (n := n))) N hh
  have hhalf : h ≤ x^(θ+ε) := by
    dsimp [h]
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx hsqrt_exp
  have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset]
  let avg := (rieszMean a (x+h) - rieszMean a x)/h
  change |∑ n ∈ Finset.Ioc 0 N, a n| ≤ _
  calc
    _ = |avg - (avg - ∑ n ∈ Finset.Ioc 0 N, a n)| := by ring_nf
    _ ≤ |avg| + |avg - ∑ n ∈ Finset.Ioc 0 N, a n| := abs_sub _ _
    _ ≤ (144*k*C*W)*x^(θ+ε) + x^(θ+ε) := add_le_add hm (herror.trans hhalf)
    _ = _ := by dsimp only [x]; ring

end D5.S3.Weil.ZetaPntBounds.MobiusShortAverage
