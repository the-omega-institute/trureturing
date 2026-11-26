/- GID: D5/S3/Analytic/StieltjesEndpointL2
   generality: G
   mirror-B: D5/B/S3/Analytic/StieltjesEndpointL2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic, mathlib/module/Mathlib.MeasureTheory.Function.L2Space]
   utility: none
   digest: A pointwise L2 cap yields a logarithmic Stieltjes endpoint bound. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import D5.S3.Analytic.Interpolation.CapWeightedEnergy
import D5.S3.Analytic.PolynomialL2Derivative

/-!
# The Stieltjes endpoint estimate from a pointwise L² cap

The cutoff is `b / M²` on `[0,b]`. The cap controls the first piece, and
Hölder with exponents `(2, 2)` controls the second. In the polynomial
application, the degree cap comes from the D5 derivative estimate and FTC.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace D5.S3.Analytic.StieltjesEndpointL2

/-- The real L² norm on `[0,b]`. -/
def l2Norm (b : ℝ) (q : ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ t in (0 : ℝ)..b, q t ^ 2)

private lemma inv_sqrt_eq_rpow {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t)⁻¹ = t ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg ht, Real.sqrt_eq_rpow]

private lemma intervalIntegrable_inv_sqrt {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Real.sqrt t)⁻¹) volume 0 b := by
  apply (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b)
    (r := -(1 / 2 : ℝ)) (by norm_num)).congr
  rw [uIoc_of_le hb]
  exact fun t ht => (inv_sqrt_eq_rpow ht.1.le).symm

private lemma integral_inv_sqrt {b : ℝ} (hb : 0 < b) :
    (∫ t : ℝ in 0..b, (Real.sqrt t)⁻¹) = 2 * Real.sqrt b := by
  have hpower :=
    (D5.S3.Analytic.Interpolation.CapWeightedEnergy.power_integral_near
      (1 / 2) b (by norm_num) hb).2
  rw [← intervalIntegral.integral_of_le hb.le] at hpower
  calc
    _ = ∫ t : ℝ in 0..b, t ^ (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hb.le]
      exact fun t ht => inv_sqrt_eq_rpow ht.1
    _ = 2 * Real.sqrt b := by
      rw [hpower, show 1 - (1 / 2 : ℝ) = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
      ring

/-- Continuity on the closed interval suffices for the integrable endpoint singularity. -/
private lemma intervalIntegrable_div_sqrt {b : ℝ} (hb : 0 ≤ b) {q : ℝ → ℝ}
    (hq : ContinuousOn q (Icc 0 b)) :
    IntervalIntegrable (fun t => q t / Real.sqrt t) volume 0 b := by
  simpa only [div_eq_mul_inv] using
    (intervalIntegrable_inv_sqrt hb).continuousOn_mul (by simpa only [uIcc_of_le hb] using hq)

private lemma integral_mul_le_sqrt_mul_sqrt {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hf0 : ∀ t ∈ Icc a b, 0 ≤ f t) (hg0 : ∀ t ∈ Icc a b, 0 ≤ g t) :
    (∫ t in a..b, f t * g t) ≤
      Real.sqrt (∫ t in a..b, f t ^ 2) * Real.sqrt (∫ t in a..b, g t ^ 2) := by
  let μ := volume.restrict (Ioc a b)
  have mem {h : ℝ → ℝ} (hc : ContinuousOn h (Icc a b)) :
      MemLp h (ENNReal.ofReal 2) μ := by
    have hint := (hc.pow 2).intervalIntegrable_of_Icc hab (μ := volume)
    have hm : AEStronglyMeasurable h μ :=
      (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    simpa using (memLp_two_iff_integrable_sq hm).2 hint.1
  have hnonneg {h : ℝ → ℝ} (hh : ∀ t ∈ Icc a b, 0 ≤ h t) : 0 ≤ᵐ[μ] h :=
    ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => hh t (Ioc_subset_Icc_self ht))
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (hnonneg hf0) (hnonneg hg0) (mem hf) (mem hg)
  simpa only [intervalIntegral.integral_of_le hab, μ, Real.rpow_two, ← Real.sqrt_eq_rpow]
    using hcs

private lemma integral_inv_sqrt_sq {s b : ℝ} (hs : 0 < s) (hsb : s ≤ b) :
    (∫ t in s..b, ((Real.sqrt t)⁻¹) ^ 2) = Real.log (b / s) := by
  calc
    _ = ∫ t in s..b, t⁻¹ := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hsb]
      intro t ht
      change ((Real.sqrt t)⁻¹) ^ 2 = t⁻¹
      rw [inv_pow, Real.sq_sqrt (hs.le.trans ht.1)]
    _ = _ := integral_inv_of_pos hs (hs.trans_le hsb)

/-- Endpoint estimate on a cutoff interval with the scale-invariant pointwise cap. -/
theorem integral_div_sqrt_le_of_pos {b M : ℝ} (hb : 0 < b) (hM : 1 ≤ M) {q : ℝ → ℝ}
    (hq : ContinuousOn q (Icc 0 b)) (hq0 : ∀ t ∈ Icc 0 b, 0 ≤ q t)
    (hcap : ∀ t ∈ Icc 0 b, q t ≤ M / Real.sqrt b * l2Norm b q) :
    (∫ t in (0 : ℝ)..b, q t / Real.sqrt t) ≤
      (2 + Real.sqrt (2 * Real.log M)) * l2Norm b q := by
  let s : ℝ := b * (M ^ 2)⁻¹
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hs : 0 < s := mul_pos hb (inv_pos.mpr (pow_pos hMpos _))
  have hM2 : 1 ≤ M ^ 2 := by nlinarith [sq_nonneg (M - 1)]
  have hsb : s ≤ b := by
    calc
      s ≤ b * 1 := mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hM2) hb.le
      _ = b := mul_one b
  have hsubNear : Icc (0 : ℝ) s ⊆ Icc 0 b := Icc_subset_Icc_right hsb
  have hsubFar : Icc s b ⊆ Icc 0 b := Icc_subset_Icc_left hs.le
  have hnearInt := intervalIntegrable_div_sqrt hs.le (hq.mono hsubNear)
  have hfarInt := (intervalIntegrable_div_sqrt hb.le hq).mono_set (c := s) (d := b)
    (by simpa only [uIcc_of_le hsb, uIcc_of_le hb.le] using hsubFar)
  have hsSqrt : Real.sqrt s = Real.sqrt b * M⁻¹ := by
    dsimp [s]
    rw [Real.sqrt_mul hb.le, Real.sqrt_inv, Real.sqrt_sq hMpos.le]
  have hnear : (∫ t in (0 : ℝ)..s, q t / Real.sqrt t) ≤ 2 * l2Norm b q := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..s, (M / Real.sqrt b * l2Norm b q) * (Real.sqrt t)⁻¹ := by
        apply intervalIntegral.integral_mono_on hs.le hnearInt
          ((intervalIntegrable_inv_sqrt hs.le).const_mul _)
        intro t ht
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (hcap t (hsubNear ht))
          (inv_nonneg.mpr (Real.sqrt_nonneg _))
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_inv_sqrt hs, hsSqrt]
        field_simp [hMpos.ne', (Real.sqrt_pos.mpr hb).ne'] <;> ring
  have hqSqInt := (hq.pow 2).intervalIntegrable_of_Icc hb.le (μ := volume)
  have hqEnergy :
      (∫ t in s..b, q t ^ 2) ≤ ∫ t in (0 : ℝ)..b, q t ^ 2 := by
    exact intervalIntegral.integral_mono_interval hs.le hsb le_rfl
      (ae_of_all _ fun t => sq_nonneg (q t)) hqSqInt
  have hlog : Real.log (b / s) = 2 * Real.log M := by
    have hratio : b / s = M ^ 2 := by
      dsimp [s]
      field_simp [hb.ne', hMpos.ne']
    rw [hratio, Real.log_pow]
    norm_num
  have hweight : ContinuousOn (fun t : ℝ => (Real.sqrt t)⁻¹) (Icc s b) :=
    Real.continuous_sqrt.continuousOn.inv₀
      (fun _ ht => (Real.sqrt_pos.mpr (hs.trans_le ht.1)).ne')
  have hfar : (∫ t in s..b, q t / Real.sqrt t) ≤
      Real.sqrt (2 * Real.log M) * l2Norm b q := by
    calc
      _ ≤ Real.sqrt (∫ t in s..b, q t ^ 2) *
          Real.sqrt (∫ t in s..b, ((Real.sqrt t)⁻¹) ^ 2) := by
        simpa only [div_eq_mul_inv] using
          integral_mul_le_sqrt_mul_sqrt hsb (hq.mono hsubFar) hweight
            (fun t ht => hq0 t (hsubFar ht)) (fun t _ => inv_nonneg.mpr (Real.sqrt_nonneg t))
      _ = Real.sqrt (∫ t in s..b, q t ^ 2) * Real.sqrt (2 * Real.log M) := by
        rw [integral_inv_sqrt_sq hs hsb, hlog]
      _ ≤ _ := by
        rw [mul_comm (Real.sqrt (2 * Real.log M)), l2Norm]
        exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hqEnergy) (Real.sqrt_nonneg _)
  rw [← intervalIntegral.integral_add_adjacent_intervals hnearInt hfarInt, add_mul]
  exact add_le_add hnear hfar

/-- The Stieltjes weight on the nonnegative real ray. -/
def stieltjesWeight (t : ℝ) : ℝ := (Real.sqrt (t * (1 + t)))⁻¹

private lemma measurable_stieltjesWeight : Measurable stieltjesWeight := by
  unfold stieltjesWeight
  fun_prop

private lemma stieltjesWeight_nonneg (t : ℝ) : 0 ≤ stieltjesWeight t :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

private lemma stieltjesWeight_le_inv_sqrt {t : ℝ} (ht : 0 ≤ t) :
    stieltjesWeight t ≤ (Real.sqrt t)⁻¹ := by
  rcases ht.eq_or_lt with hzero | hpos
  · simp [← hzero, stieltjesWeight]
  · apply inv_anti₀ (Real.sqrt_pos.mpr hpos)
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])

/-- Integrability and the Stieltjes-weight estimate for the norm of a continuous profile. -/
theorem integral_stieltjes_mul_norm_le {E : Type*} [NormedAddCommGroup E]
    {b M : ℝ} (hb : 0 < b) (hM : 1 ≤ M) {F : ℝ → E}
    (hF : ContinuousOn F (Icc 0 b))
    (hcap : ∀ t ∈ Icc 0 b, ‖F t‖ ≤ M / Real.sqrt b * l2Norm b (fun u => ‖F u‖)) :
    IntervalIntegrable (fun t => stieltjesWeight t * ‖F t‖) volume 0 b ∧
      (∫ t in (0 : ℝ)..b, stieltjesWeight t * ‖F t‖) ≤
        (2 + Real.sqrt (2 * Real.log M)) * l2Norm b (fun t => ‖F t‖) := by
  have hmodel := intervalIntegrable_div_sqrt hb.le hF.norm
  have hle t (ht : t ∈ Icc 0 b) :
      stieltjesWeight t * ‖F t‖ ≤ ‖F t‖ / Real.sqrt t := by
    rw [div_eq_mul_inv, mul_comm ‖F t‖]
    exact mul_le_mul_of_nonneg_right (stieltjesWeight_le_inv_sqrt ht.1) (norm_nonneg _)
  have hst : IntervalIntegrable (fun t => stieltjesWeight t * ‖F t‖) volume 0 b := by
    apply hmodel.mono_fun'
    · rw [uIoc_of_le hb.le]
      exact measurable_stieltjesWeight.aestronglyMeasurable.mul
        ((hF.norm.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    · rw [uIoc_of_le hb.le]
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro t ht
      change ‖stieltjesWeight t * ‖F t‖‖ ≤ ‖F t‖ / Real.sqrt t
      rw [Real.norm_of_nonneg (mul_nonneg (stieltjesWeight_nonneg t) (norm_nonneg _))]
      exact hle t (Ioc_subset_Icc_self ht)
  exact ⟨hst, (intervalIntegral.integral_mono_on hb.le hst hmodel hle).trans
    (integral_div_sqrt_le_of_pos hb hM hF.norm (fun _ _ => norm_nonneg _) hcap)⟩

/-- The Bochner-integral estimate for a real or vector-valued profile against the
Stieltjes weight. -/
theorem norm_integral_stieltjes_smul_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {b M : ℝ} (hb : 0 < b) (hM : 1 ≤ M)
    {F : ℝ → E} (hF : ContinuousOn F (Icc 0 b))
    (hcap : ∀ t ∈ Icc 0 b, ‖F t‖ ≤ M / Real.sqrt b * l2Norm b (fun u => ‖F u‖)) :
    IntervalIntegrable (fun t => stieltjesWeight t • F t) volume 0 b ∧
      ‖∫ t in (0 : ℝ)..b, stieltjesWeight t • F t‖ ≤
        (2 + Real.sqrt (2 * Real.log M)) * l2Norm b (fun t => ‖F t‖) := by
  obtain ⟨hi, hbound⟩ := integral_stieltjes_mul_norm_le hb hM hF hcap
  have hnorm : ∀ t, ‖stieltjesWeight t • F t‖ = stieltjesWeight t * ‖F t‖ := by
    intro t
    rw [norm_smul, Real.norm_of_nonneg (stieltjesWeight_nonneg t)]
  constructor
  · apply hi.mono_fun'
    · rw [uIoc_of_le hb.le]
      exact measurable_stieltjesWeight.aestronglyMeasurable.smul
        ((hF.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    · exact ae_of_all _ fun t => (hnorm t).le
  · calc
      _ ≤ ∫ t in (0 : ℝ)..b, stieltjesWeight t * ‖F t‖ := by
        simpa only [hnorm] using intervalIntegral.norm_integral_le_integral_norm
          (f := fun t => stieltjesWeight t • F t) hb.le (μ := volume)
      _ ≤ _ := hbound

private lemma integral_le_l2Norm {q : ℝ → ℝ} (hq : ContinuousOn q (Icc 0 1))
    (hq0 : ∀ t ∈ Icc 0 1, 0 ≤ q t) :
    (∫ t in (0 : ℝ)..1, q t) ≤ l2Norm 1 q := by
  have h := integral_mul_le_sqrt_mul_sqrt (zero_le_one : (0 : ℝ) ≤ 1)
    hq (g := fun _ => (1 : ℝ)) continuousOn_const hq0 (fun _ _ => zero_le_one)
  simpa [l2Norm, intervalIntegral.integral_const] using h

open Polynomial
open D5.S3.Analytic.PolynomialL2Derivative (eval_continuous
  complex_polynomial_derivative_l2_of_degree)

/-- FTC and the derivative L² estimate give the cap `1 + d²` for degree below `d`. -/
theorem polynomial_norm_le_cap (d : ℕ) (p : ℂ[X]) (hp : p.degree < (d : WithBot ℕ))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖p.eval (x : ℂ)‖ ≤ (1 + (d : ℝ) ^ 2) * l2Norm 1 (fun t => ‖p.eval (t : ℂ)‖) := by
  let q : ℝ → ℝ := fun t => ‖p.eval (t : ℂ)‖
  let r : ℝ → ℝ := fun t => ‖p.derivative.eval (t : ℂ)‖
  have hq : Continuous q := (eval_continuous p).norm
  have hr : Continuous r := (eval_continuous p.derivative).norm
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hordered {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      ‖p.eval (b : ℂ) - p.eval (a : ℂ)‖ ≤ ∫ t in (0 : ℝ)..1, r t := by
    have hFTC : (∫ t in a..b, p.derivative.eval (t : ℂ)) = p.eval (b : ℂ) - p.eval (a : ℂ) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => (p.hasDerivAt (t : ℂ)).comp_ofReal)
        ((eval_continuous p.derivative).intervalIntegrable a b)
    rw [← hFTC]
    exact (intervalIntegral.norm_integral_le_integral_norm hab).trans
      (intervalIntegral.integral_mono_interval ha hab hb
        (ae_of_all _ fun t => norm_nonneg (p.derivative.eval (t : ℂ)))
        (hr.intervalIntegrable 0 1))
  have hpointwise (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      q x ≤ q y + ∫ t in (0 : ℝ)..1, r t := by
    have hdiff : ‖p.eval (x : ℂ) - p.eval (y : ℂ)‖ ≤ ∫ t in (0 : ℝ)..1, r t := by
      rcases le_total y x with hyx | hxy
      · exact hordered hy.1 hyx hx.2
      · rw [norm_sub_rev]
        exact hordered hx.1 hxy hy.2
    calc
      q x = ‖(p.eval (x : ℂ) - p.eval (y : ℂ)) + p.eval (y : ℂ)‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖p.eval (x : ℂ) - p.eval (y : ℂ)‖ + q y := norm_add_le _ _
      _ ≤ _ := by simpa only [add_comm] using add_le_add_right hdiff (q y)
  have hqInt := hq.intervalIntegrable (μ := volume) 0 1
  have havg := intervalIntegral.integral_mono_on h01
    (intervalIntegrable_const (c := q x))
    (hqInt.add (intervalIntegrable_const (c := ∫ t in (0 : ℝ)..1, r t))) hpointwise
  rw [intervalIntegral.integral_add hqInt intervalIntegrable_const] at havg
  have havg' : q x ≤ (∫ t in (0 : ℝ)..1, q t) + ∫ t in (0 : ℝ)..1, r t := by
    simpa [intervalIntegral.integral_const] using havg
  have hderiv : l2Norm 1 r ≤ (d : ℝ) ^ 2 * l2Norm 1 q := by
    have h := Real.sqrt_le_sqrt (complex_polynomial_derivative_l2_of_degree d p hp)
    change l2Norm 1 r ≤ Real.sqrt ((d : ℝ) ^ 4 * (∫ t in (0 : ℝ)..1, q t ^ 2)) at h
    rwa [Real.sqrt_mul (by positivity), show (d : ℝ) ^ 4 = ((d : ℝ) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg _)] at h
  calc
    q x ≤ (∫ t in (0 : ℝ)..1, q t) + ∫ t in (0 : ℝ)..1, r t := havg'
    _ ≤ l2Norm 1 q + (d : ℝ) ^ 2 * l2Norm 1 q :=
      add_le_add (integral_le_l2Norm hq.continuousOn (fun _ _ => norm_nonneg _))
        ((integral_le_l2Norm hr.continuousOn (fun _ _ => norm_nonneg _)).trans hderiv)
    _ = _ := by rw [add_mul, one_mul]

/-- Complex-polynomial Stieltjes estimate. For degree at most `n`, take `d = n + 1`. -/
theorem integral_stieltjes_polynomial_norm_le (d : ℕ) (p : ℂ[X])
    (hp : p.degree < (d : WithBot ℕ)) :
    IntervalIntegrable (fun t : ℝ => stieltjesWeight t * ‖p.eval (t : ℂ)‖) volume 0 1 ∧
      (∫ t in (0 : ℝ)..1, stieltjesWeight t * ‖p.eval (t : ℂ)‖) ≤
        (2 + Real.sqrt (2 * Real.log (1 + (d : ℝ) ^ 2))) *
          l2Norm 1 (fun t => ‖p.eval (t : ℂ)‖) := by
  apply integral_stieltjes_mul_norm_le (b := 1) (M := 1 + (d : ℝ) ^ 2)
    zero_lt_one (by nlinarith [sq_nonneg (d : ℝ)]) (eval_continuous p).continuousOn
  intro t ht
  simpa only [Real.sqrt_one, div_one] using polynomial_norm_le_cap d p hp ht

end D5.S3.Analytic.StieltjesEndpointL2
