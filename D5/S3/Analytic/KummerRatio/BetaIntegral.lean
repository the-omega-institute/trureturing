/- GID: D5/S3/Analytic/KummerRatio/BetaIntegral
   generality: G
   mirror-B: D5/B/S3/Analytic/KummerRatio/BetaIntegral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Beta, mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence]
   utility: none
   digest: Real beta moments and the beta integral representation of the Kummer series. -/

import D5.S3.Analytic.KummerRatio.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Set MeasureTheory
open scoped Real
open D5.S3.Analytic.KummerRatio.Defs

namespace D5.S3.Analytic.KummerRatio.BetaIntegral

/-- The real beta integral is the quotient of the corresponding Gamma values. -/
theorem integral_beta {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ t in (0:ℝ)..1, t^(p-1) * (1-t)^(q-1)) =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p+q) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have hconv : (∫ t in (0:ℝ)..1, ((t^(p-1) * (1-t)^(q-1) : ℝ) : ℂ)) =
      Complex.betaIntegral p q := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro t ht
    dsimp only
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht.1),
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2.le)]
    push_cast
    rfl
  rw [hconv, Complex.betaIntegral_eq_Gamma_mul_div _ _ hp hq]
  push_cast
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_add,
      Complex.Gamma_ofReal]

/-- Integrability of the real beta density for positive shape parameters. -/
theorem intervalIntegrable_beta {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntervalIntegrable (fun t : ℝ => t^(p-1) * (1-t)^(q-1)) volume 0 1 := by
  have hi := Complex.betaIntegral_convergent (u := p) (v := q) hp hq
  have hr : IntervalIntegrable (fun t : ℝ =>
      ((t:ℂ)^((p:ℂ)-1) * (1-(t:ℂ))^((q:ℂ)-1)).re) volume 0 1 :=
    ⟨hi.1.re, hi.2.re⟩
  apply hr.congr
  intro t ht
  dsimp only
  rw [Set.uIoc_of_le zero_le_one] at ht
  have ht0 := ht.1.le
  have ht1 := sub_nonneg.mpr ht.2
  have he : (t:ℂ)^((p:ℂ)-1) * (1-(t:ℂ))^((q:ℂ)-1) =
      ((t^(p-1) * (1-t)^(q-1) : ℝ) : ℂ) := by
    push_cast
    rw [Complex.ofReal_cpow ht0, Complex.ofReal_cpow ht1]
    push_cast
    rfl
  rw [he]
  rfl

lemma gamma_pochhammer {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Real.Gamma (s+n) = (ascPochhammer ℝ n).eval s * Real.Gamma s := by
  have hg : Real.Gamma (s+n) / Real.Gamma s = (ascPochhammer ℝ n).eval s := by
    apply Complex.ofReal_injective
    push_cast
    rw [← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.Gamma_add_nat_div_Gamma_eq]
    · rw [ascPochhammer_eval₂ Complex.ofRealHom]
      exact Polynomial.eval₂_at_apply _ _
    · intro k hk
      have h := congrArg Complex.re hk
      simp at h
      linarith [Nat.cast_nonneg (α := ℝ) k]
  exact (div_eq_iff (Real.Gamma_pos_of_pos hs).ne').mp hg

private lemma integral_beta_monomial {s d : ℝ} (hs : 0 < s) (hd : 0 < d)
    (x : ℝ) (n : ℕ) :
    (∫ t in (0:ℝ)..1, ((x*t)^n / (n.factorial:ℝ)) *
        (t^(s-1) * (1-t)^(d-1))) =
      (x^n / (n.factorial:ℝ)) *
        (Real.Gamma (s+n) * Real.Gamma d / Real.Gamma (s+n+d)) := by
  rw [← integral_beta (by positivity : 0 < s+(n:ℝ)) hd,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro t ht
  dsimp only
  rw [show s+(n:ℝ)-1 = (n:ℝ)+(s-1) by ring,
    Real.rpow_add ht.1, Real.rpow_natCast, mul_pow]
  ring

/-- The beta integral represents Kummer's function when the upper parameter
lies strictly between zero and the lower parameter. -/
theorem kummer_eq_betaIntegral {s c : ℝ} (hs : 0 < s) (hsc : s < c) (x : ℝ) :
    kummer s c x = Real.Gamma c / (Real.Gamma s * Real.Gamma (c-s)) *
      ∫ t in (0:ℝ)..1, Real.exp (x*t) * t^(s-1) * (1-t)^(c-s-1) := by
  let w : ℝ → ℝ := fun t => t^(s-1) * (1-t)^(c-s-1)
  let F : ℕ → ℝ → ℝ := fun n t => (x*t)^n / (n.factorial:ℝ) * w t
  let b : ℕ → ℝ → ℝ := fun n t => |x|^n / (n.factorial:ℝ) * w t
  have hc : 0 < c := lt_trans hs hsc
  have hd : 0 < c-s := sub_pos.mpr hsc
  have hw := intervalIntegrable_beta hs hd
  have hexp (z : ℝ) : HasSum (fun n : ℕ => z^n / (n.factorial:ℝ)) (Real.exp z) := by
    simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp z
  have hb (t : ℝ) : HasSum (fun n => b n t) (Real.exp |x| * w t) :=
    (hexp |x|).mul_right (w t)
  have hsum : HasSum (fun n => ∫ t in (0:ℝ)..1, F n t)
      (∫ t in (0:ℝ)..1, Real.exp (x*t) * w t) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence b
    · intro n
      apply Measurable.aestronglyMeasurable
      dsimp [F, w]
      fun_prop
    · intro n
      filter_upwards [] with t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hw0 : 0 ≤ w t := mul_nonneg
        (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _)
      dsimp [F, b]
      rw [abs_mul, abs_div, abs_pow, abs_of_nonneg (show (0:ℝ) ≤ (n.factorial:ℝ) from Nat.cast_nonneg _),
        abs_of_nonneg hw0]
      apply mul_le_mul_of_nonneg_right _ hw0
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ (abs_nonneg _) _
      rw [abs_mul, abs_of_pos ht.1]
      exact mul_le_of_le_one_right (abs_nonneg _) ht.2
    · exact Filter.Eventually.of_forall (fun t _ => (hb t).summable)
    · convert hw.const_mul (Real.exp |x|) using 1
      exact funext (fun t => (hb t).tsum_eq)
    · exact Filter.Eventually.of_forall (fun t _ => (hexp (x*t)).mul_right (w t))
  have hm (n : ℕ) : Real.Gamma c / (Real.Gamma s * Real.Gamma (c-s)) *
      (∫ t in (0:ℝ)..1, F n t) = kummerCoeff s c n * x^n := by
    dsimp only [F, w]
    rw [integral_beta_monomial hs hd, show s+(n:ℝ)+(c-s) = c+n by ring,
      gamma_pochhammer hs, gamma_pochhammer hc]
    unfold kummerCoeff
    have hgs := (Real.Gamma_pos_of_pos hs).ne'
    have hgc := (Real.Gamma_pos_of_pos hc).ne'
    have hgd := (Real.Gamma_pos_of_pos hd).ne'
    have hpc := (ascPochhammer_pos n c hc).ne'
    have hfac : (n.factorial:ℝ) ≠ 0 := by positivity
    field_simp
  have hnormalized := hsum.mul_left (Real.Gamma c / (Real.Gamma s * Real.Gamma (c-s)))
  simp_rw [hm] at hnormalized
  simpa only [kummer, w, mul_assoc] using hnormalized.tsum_eq

end D5.S3.Analytic.KummerRatio.BetaIntegral
