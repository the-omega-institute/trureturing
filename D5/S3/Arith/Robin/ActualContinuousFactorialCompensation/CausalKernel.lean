/- GID: D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/CausalKernel
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualContinuousFactorialCompensation/CausalKernel
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The actual causal logarithmic pullback is globally continuous, locally absolutely continuous and W1,1 with both L1 budgets at most four gamma plus sixteen. -/

import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
Integrated by relocating the causal construction of the immutable source
candidate, with only the two consumed arithmetic seams exposed in its owner.
Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. The owner
contract is checked by the scoped Lean/report workflow; registration binding
remains a separate unfinished audit.

The full primitive, origin join, genuine ae derivative and both global budgets
remain on the live construction path. Arithmetic regularity and bounds are
consumed through compensation; G_eq_integral and slope_measurable are the only
additional public seams. Supplier attribution remains at the arithmetic owner,
including its reference to Terence Tao / Apache-2.0 at LogConvolutionMassExpansion.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped BigOperators Topology ArithmeticFunction

namespace D5.S3.Arith.Robin.ActualContinuousFactorialCompensation

def r (t : ℝ) : ℝ := if 0 ≤ t then Real.exp (-t / 2) * G (Real.exp t) else 0
def rSlope (t : ℝ) : ℝ := if 0 ≤ t then
  Real.exp (-t / 2) * (Real.exp t * slope (Real.exp t) - G (Real.exp t) / 2)
  else 0

private lemma r_continuous : Continuous r := by
  have hc : ContinuousOn (fun t : ℝ => Real.exp (-t / 2) * G (Real.exp t)) (Ici 0) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-t / 2))).continuousOn.mul
      ((compensation.2.1).comp Real.continuous_exp.continuousOn
        (fun t ht => Real.one_le_exp_iff.mpr ht))
  unfold r
  apply continuous_if
  · intro t ht
    change t ∈ frontier (Ici (0 : ℝ)) at ht
    rw [frontier_Ici] at ht
    have ht0 : t = 0 := Set.mem_singleton_iff.mp ht
    simp only [ht0, neg_zero, zero_div, Real.exp_zero, one_mul, compensation.1]
  · simpa only [show {t : ℝ | 0 ≤ t} = Ici 0 from rfl, closure_Ici] using hc
  · exact continuousOn_const

private lemma rSlope_measurable : Measurable rSlope := by
  have hm : Measurable (fun t : ℝ =>
      if 0 ≤ t then Real.exp (-t / 2) * Real.exp t * slope (Real.exp t) else 0) :=
    Measurable.ite measurableSet_Ici
      (((by fun_prop : Measurable (fun t : ℝ => Real.exp (-t / 2))).mul
        Real.measurable_exp).mul (slope_measurable.comp Real.measurable_exp))
      measurable_const
  have he : rSlope = fun t =>
      (if 0 ≤ t then Real.exp (-t / 2) * Real.exp t * slope (Real.exp t) else 0) - r t / 2 := by
    funext t
    by_cases ht : 0 ≤ t
    · simp only [rSlope, r, if_pos ht]
      ring
    · simp only [rSlope, r, if_neg ht, zero_div, sub_self]
  rw [he]
  exact hm.sub (r_continuous.measurable.div_const 2)

private def valueMajorant (t : ℝ) : ℝ :=
  Real.exp (-t / 2) * ((gamma + 2) * t + t ^ 2 / 2)

private def slopeMajorant (t : ℝ) : ℝ :=
  Real.exp (-t / 2) * (gamma + 2 + t + ((gamma + 2) * t + t ^ 2 / 2) / 2)

private lemma r_bound {t : ℝ} (ht : 0 ≤ t) : |r t| ≤ valueMajorant t := by
  rw [r, if_pos ht, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (compensation.2.2.2.2.1 t ht) (Real.exp_pos _).le

private lemma exp_slope_bound {t : ℝ} (ht : 0 ≤ t) :
    |Real.exp t * slope (Real.exp t)| ≤ gamma + 2 + t := by
  have hb := (compensation.2.2.2.2.2.1 (Real.exp t)
    (Real.one_le_exp_iff.mpr ht)).2
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp t * ((gamma + 2 + Real.log (Real.exp t)) / Real.exp t) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by rw [Real.log_exp]; field_simp [Real.exp_ne_zero t]

private lemma rSlope_bound {t : ℝ} (ht : 0 ≤ t) : |rSlope t| ≤ slopeMajorant t := by
  have hG := compensation.2.2.2.2.1 t ht
  have hs := exp_slope_bound ht
  rw [rSlope, if_pos ht, abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    _ ≤ |Real.exp t * slope (Real.exp t)| + |G (Real.exp t) / 2| := abs_sub _ _
    _ ≤ gamma + 2 + t + ((gamma + 2) * t + t ^ 2 / 2) / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_le_add hs (div_le_div_of_nonneg_right hG (by norm_num))

private lemma exp_moment_integrable (n : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t / 2) * t ^ n) (Ioi 0) := by
  have hΓ : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ n) (Ioi 0) := by
    simpa only [add_sub_cancel_right, Real.rpow_natCast] using
      Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity)
  have hh : IntegrableOn
      (fun t : ℝ => Real.exp (-(1 / 2 * t)) * (1 / 2 * t) ^ n) (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_comp_mul_left_iff
    (fun u : ℝ => Real.exp (-u) * u ^ n) 0 (a := (1 / 2 : ℝ)) (by norm_num)).mpr
      (by simpa using hΓ)
  refine (hh.mul_const ((2 : ℝ) ^ n)).congr (Eventually.of_forall ?_)
  intro t
  simp only [Function.comp_apply]
  rw [mul_assoc, ← mul_pow,
    show -(1 / 2 * t : ℝ) = -t / 2 by ring,
    show ((1 / 2 : ℝ) * t) * 2 = t by ring]

private lemma exp_moment_integral (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t / 2) * t ^ n) =
      (2 : ℝ) ^ (n + 1) * n.factorial := by
  have hΓ := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n : ℝ) + 1) (r := (1 / 2 : ℝ)) (by positivity) (by norm_num)
  convert hΓ using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [add_sub_cancel_right, Real.rpow_natCast]
    have he : -t / 2 = -((1 / 2 : ℝ) * t) := by ring
    rw [he, mul_comm]
  · rw [Real.Gamma_nat_eq_factorial]
    norm_num only [one_div_div, div_one]
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]

private lemma majorant_data :
    IntegrableOn valueMajorant (Ioi (0 : ℝ)) ∧
    IntegrableOn slopeMajorant (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), valueMajorant t) = 4 * gamma + 16 ∧
    (∫ t in Ioi (0 : ℝ), slopeMajorant t) = 4 * gamma + 16 := by
  have hv : valueMajorant = fun t =>
      (gamma + 2) * (Real.exp (-t / 2) * t ^ 1) +
        (1 / 2 : ℝ) * (Real.exp (-t / 2) * t ^ 2) := by
    funext t
    dsimp [valueMajorant]
    ring
  have hs : slopeMajorant = fun t =>
      (gamma + 2) * (Real.exp (-t / 2) * t ^ 0) +
        (1 + (gamma + 2) / 2) * (Real.exp (-t / 2) * t ^ 1) +
          (1 / 4 : ℝ) * (Real.exp (-t / 2) * t ^ 2) := by
    funext t
    dsimp [slopeMajorant]
    ring
  have hi₀ := exp_moment_integrable 0
  have hi₁ := exp_moment_integrable 1
  have hi₂ := exp_moment_integrable 2
  have hiv := (hi₁.const_mul (gamma + 2)).add (hi₂.const_mul (1 / 2 : ℝ))
  have his := ((hi₀.const_mul (gamma + 2)).add
    (hi₁.const_mul (1 + (gamma + 2) / 2))).add (hi₂.const_mul (1 / 4 : ℝ))
  refine ⟨hv.symm ▸ hiv, hs.symm ▸ his, ?_, ?_⟩
  · rw [hv, integral_add (hi₁.const_mul (gamma + 2)) (hi₂.const_mul (1 / 2 : ℝ)),
      integral_const_mul, integral_const_mul, exp_moment_integral, exp_moment_integral]
    norm_num
    <;> ring
  · rw [hs]
    let f₀ : ℝ → ℝ := fun t =>
      (gamma + 2) * (Real.exp (-t / 2) * t ^ 0)
    let f₁ : ℝ → ℝ := fun t =>
      (1 + (gamma + 2) / 2) * (Real.exp (-t / 2) * t ^ 1)
    let f₂ : ℝ → ℝ := fun t =>
      (1 / 4 : ℝ) * (Real.exp (-t / 2) * t ^ 2)
    have hsplit :
        (∫ t in Ioi (0 : ℝ), (f₀ + f₁ + f₂) t) = 4 * gamma + 16 := by
      calc
        (∫ t in Ioi (0 : ℝ), (f₀ + f₁ + f₂) t) =
            (∫ t in Ioi (0 : ℝ), (f₀ + f₁) t) +
              ∫ t in Ioi (0 : ℝ), f₂ t := by
          simpa only [Pi.add_apply] using
            (integral_add' (μ := volume.restrict (Ioi (0 : ℝ)))
              ((hi₀.const_mul (gamma + 2)).add
                (hi₁.const_mul (1 + (gamma + 2) / 2)))
              (hi₂.const_mul (1 / 4 : ℝ)))
        _ = ((∫ t in Ioi (0 : ℝ), f₀ t) +
              ∫ t in Ioi (0 : ℝ), f₁ t) +
              ∫ t in Ioi (0 : ℝ), f₂ t := by
          rw [integral_add' (μ := volume.restrict (Ioi (0 : ℝ)))
            (hi₀.const_mul (gamma + 2))
            (hi₁.const_mul (1 + (gamma + 2) / 2))]
        _ = 4 * gamma + 16 := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul,
            exp_moment_integral, exp_moment_integral, exp_moment_integral]
          norm_num
          <;> ring
    simpa [f₀, f₁, f₂, Pi.add_apply] using hsplit

private lemma causal_integrable {f b : ℝ → ℝ} (hm : Measurable f)
    (hz : ∀ t : ℝ, t < 0 → f t = 0) (hb : IntegrableOn b (Ioi (0 : ℝ)))
    (hfb : ∀ t : ℝ, 0 ≤ t → |f t| ≤ b t) :
    Integrable f ∧ (∫ t, |f t|) ≤ ∫ t in Ioi (0 : ℝ), b t := by
  have hi : IntegrableOn f (Ioi (0 : ℝ)) := by
    apply hb.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Real.norm_eq_abs] using hfb t ht.le
  have hi' : IntegrableOn f (Ici (0 : ℝ)) := by
    simpa only [IntegrableOn, restrict_Ioi_eq_restrict_Ici] using hi
  have hind : (Ici (0 : ℝ)).indicator f = f := by
    funext t
    by_cases ht : 0 ≤ t
    · simp [ht]
    · simp [ht, hz t (lt_of_not_ge ht)]
  have hf : Integrable f := by
    rw [← hind]
    exact hi'.integrable_indicator measurableSet_Ici
  refine ⟨hf, ?_⟩
  have habs : (Ici (0 : ℝ)).indicator (fun t => |f t|) = fun t => |f t| := by
    funext t
    by_cases ht : 0 ≤ t
    · simp [ht]
    · simp [ht, hz t (lt_of_not_ge ht)]
  calc
    _ = ∫ t in Ici (0 : ℝ), |f t| := by
      nth_rw 1 [← habs]
      rw [integral_indicator measurableSet_Ici]
    _ = ∫ t in Ioi (0 : ℝ), |f t| := integral_Ici_eq_integral_Ioi
    _ ≤ _ := setIntegral_mono_on hi.abs hb measurableSet_Ioi (fun t ht => hfb t ht.le)

/-- Consumed value/density estimate. Identification with the actual derivative
is performed below, through an absolutely continuous primitive. -/
private lemma causal_budgets :
    Continuous r ∧ r 0 = 0 ∧ Integrable r ∧ Integrable rSlope ∧
    (∫ t : ℝ, |r t|) ≤ 4 * gamma + 16 ∧
    (∫ t : ℝ, |rSlope t|) ≤ 4 * gamma + 16 := by
  have hr := causal_integrable r_continuous.measurable
    (fun t ht => by simp [r, not_le.mpr ht]) majorant_data.1
    (fun _ ht => r_bound ht)
  have hd := causal_integrable rSlope_measurable
    (fun t ht => by simp [rSlope, not_le.mpr ht]) majorant_data.2.1
    (fun _ ht => rSlope_bound ht)
  refine ⟨r_continuous, ?_, hr.1, hd.1, ?_, ?_⟩
  · simp [r, compensation.1]
  · simpa only [majorant_data.2.2.1] using hr.2
  · simpa only [majorant_data.2.2.2] using hd.2

/-- The causal logarithmic pullback of the genuine arithmetic slope. -/
private def liftedSlope (t : ℝ) : ℝ :=
  if 0 ≤ t then Real.exp t * slope (Real.exp t) else 0

private def primitive (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, liftedSlope u

private lemma liftedSlope_measurable : Measurable liftedSlope := by
  exact Measurable.ite measurableSet_Ici
    (Real.measurable_exp.mul (slope_measurable.comp Real.measurable_exp)) measurable_const

private lemma liftedSlope_integrableOn (a b : ℝ) :
    IntegrableOn liftedSlope (Icc a b) := by
  let C : ℝ := gamma + 2 + max b 0
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith [Real.one_half_lt_eulerMascheroniConstant, le_max_right b 0]
  apply (integrableOn_const (C := C) (s := Icc a b)
    (by exact measure_Icc_lt_top.ne)).mono'
    liftedSlope_measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs]
  by_cases ht0 : 0 ≤ t
  · rw [liftedSlope, if_pos ht0]
    exact (exp_slope_bound ht0).trans (by dsimp [C]; linarith [ht.2, le_max_left b 0])
  · simpa only [liftedSlope, if_neg ht0, abs_zero] using hC

private lemma liftedSlope_locallyIntegrable : LocallyIntegrable liftedSlope volume := by
  intro x
  exact ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
    liftedSlope_integrableOn _ _⟩

/-- Monotone exponential change of variables needs no pointwise continuity
of the stepwise arithmetic slope. Its interval integrability is already paid. -/
private lemma primitive_formula (t : ℝ) :
    primitive t = if 0 ≤ t then G (Real.exp t) else 0 := by
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, G_eq_integral (Real.one_le_exp_iff.mpr ht)]
    have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := t) (f := Real.exp) (f' := Real.exp) (g := slope)
      Real.continuous_exp.continuousOn (fun u _ => Real.hasDerivAt_exp u)
      (fun u _ => (Real.exp_pos u).le)
    rw [Real.exp_zero] at hchange
    rw [← hchange, primitive]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    simp only [liftedSlope, if_pos hu.1, Function.comp_apply]
    ring
  · rw [if_neg ht, primitive, intervalIntegral.integral_symm]
    have hzero : (∫ u in t..(0 : ℝ), liftedSlope u) = 0 := by
      calc
        _ = ∫ _u in t..(0 : ℝ), (0 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le (le_of_lt (lt_of_not_ge ht))
          intro u hu
          simp only [liftedSlope, if_neg (not_le.mpr hu.2)]
        _ = 0 := by simp
    rw [hzero, neg_zero]

private lemma primitive_ac (a b : ℝ) : AbsolutelyContinuousOnInterval primitive a b := by
  let A : ℝ := min (min a b) 0
  let B' : ℝ := max (max a b) 0
  have hAB : A ≤ B' := (min_le_right _ _).trans (le_max_right _ _)
  have hi : IntervalIntegrable liftedSlope volume A B' :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr
      (liftedSlope_integrableOn A B')
  have hzero : (0 : ℝ) ∈ uIcc A B' := by
    rw [uIcc_of_le hAB]
    exact ⟨min_le_right _ _, le_max_right _ _⟩
  apply (hi.absolutelyContinuousOnInterval_intervalIntegral hzero).mono
  apply uIcc_subset_uIcc
  · rw [uIcc_of_le hAB]
    exact ⟨(min_le_left (min a b) 0).trans (min_le_left a b),
      (le_max_left a b).trans (le_max_left (max a b) 0)⟩
  · rw [uIcc_of_le hAB]
    exact ⟨(min_le_left (min a b) 0).trans (min_le_right a b),
      (le_max_right a b).trans (le_max_left (max a b) 0)⟩

private lemma r_eq_product : r = fun t : ℝ => Real.exp (-t / 2) * primitive t := by
  funext t
  rw [primitive_formula]
  by_cases ht : 0 ≤ t <;> simp [r, ht]

private lemma r_ac (a b : ℝ) : AbsolutelyContinuousOnInterval r a b := by
  have hw : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-t / 2)) := by fun_prop
  have ha := hw.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)
  apply (ha.mul (primitive_ac a b)).congr
  intro t _
  exact (congrFun r_eq_product t).symm

private lemma r_hasDerivAt_ae : ∀ᵐ t : ℝ, HasDerivAt r (rSlope t) t := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral liftedSlope_locallyIntegrable] with t ht
  have hU : HasDerivAt primitive (liftedSlope t) t := ht 0
  have hw : HasDerivAt (fun u : ℝ => Real.exp (-u / 2)) (-Real.exp (-t / 2) / 2) t := by
    simpa [Function.comp_def, div_eq_mul_inv] using
      (((hasDerivAt_id t).neg.div_const 2).exp)
  rw [r_eq_product]
  apply (hw.mul hU).congr_deriv
  rw [primitive_formula]
  by_cases ht0 : 0 ≤ t
  · simp only [rSlope, liftedSlope, if_pos ht0]
    ring
  · simp only [rSlope, liftedSlope, if_neg ht0, mul_zero, add_zero]

/-- The actual compensated causal kernel is locally absolutely continuous,
has the displayed genuine almost-everywhere derivative, and both global L1
norms are bounded by the same universal constant. The primitive representation
retains the causal entrance and proves that no origin jump is discarded.
The owner is compiled in the scoped integration build; registration binding remains unfinished. -/
theorem causal_kernel :
    Continuous r ∧ r 0 = 0 ∧
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval r a b) ∧
    (∀ᵐ t : ℝ, HasDerivAt r (rSlope t) t) ∧
    Integrable r ∧ Integrable (deriv r) ∧
    (∫ t : ℝ, |r t|) ≤ 4 * gamma + 16 ∧
    (∫ t : ℝ, |deriv r t|) ≤ 4 * gamma + 16 := by
  have hd : deriv r =ᵐ[volume] rSlope := r_hasDerivAt_ae.mono (fun _ ht => ht.deriv)
  have hi : Integrable (deriv r) := (integrable_congr hd).mpr causal_budgets.2.2.2.1
  have hnorm : (∫ t : ℝ, |deriv r t|) = ∫ t : ℝ, |rSlope t| := by
    apply integral_congr_ae
    filter_upwards [hd] with t ht
    rw [ht]
  refine ⟨causal_budgets.1, causal_budgets.2.1, r_ac, r_hasDerivAt_ae,
    causal_budgets.2.2.1, hi, causal_budgets.2.2.2.2.1, ?_⟩
  rw [hnorm]
  exact causal_budgets.2.2.2.2.2

end D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
