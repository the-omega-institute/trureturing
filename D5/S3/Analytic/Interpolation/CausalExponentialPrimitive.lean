/- GID: D5/S3/Analytic/Interpolation/CausalExponentialPrimitive
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/CausalExponentialPrimitive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus]
   utility: none
   digest: Exact finite causal responses and right-FTC primitive and square identities. -/

import D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
import D5.S3.Analytic.MomentOrthogonalPrimitiveGap
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.QuadraticDiscriminant

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open MeasureTheory Set Filter
open scoped BigOperators Topology
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy

namespace D5.S3.Analytic.Interpolation.MomentExponentialCoercivity

variable {I : Type u} [Fintype I]

def ramp (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, a i * (max (t - x i) 0 : ℝ)

def resolvent (lam : ℝ) (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, a i * (((1 - Real.exp (-lam * max (t - x i) 0)) / lam : ℝ) : ℂ)

def secondResolvent (lam : ℝ) (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  (ramp x a t - resolvent lam x a t) / (lam : ℂ)

def response (lam : ℝ) (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, if x i ≤ t then a i * (Real.exp (-lam * (t - x i)) : ℂ) else 0

private lemma prefix_below (x : I → ℝ) (a : I → ℂ) (t : ℝ)
    (ht : ∀ i, t < x i) : «prefix» x a t = 0 := by
  classical
  simp [«prefix», fun i => not_le.mpr (ht i)]

lemma prefix_above (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0)
    (t : ℝ) (ht : ∀ i, x i ≤ t) : «prefix» x a t = 0 := by
  classical
  simp [«prefix», ht, ha]

lemma prefix_energy_window (x : I → ℝ) (a : I → ℂ)
    (D : ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0) :
    (∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) =
      ∫ t in Icc 0 D, ‖«prefix» x a t‖ ^ 2 := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rcases lt_or_ge t 0 with ht0 | ht0
  · rw [prefix_below x a t (fun i => ht0.trans_le (hx i).1)]
    simp
  · have htD : D < t := lt_of_not_ge (fun h => ht ⟨ht0, h⟩)
    rw [prefix_above x a ha t (fun i => (hx i).2.trans htD.le)]
    simp

/-- A continuous multiplier of the actual prefix is integrable on a compact
window. This supplies every mixed term in the right-FTC energy calculation. -/
lemma prefix_mul_integrable (x : I → ℝ) (a : I → ℂ) (D : ℝ)
    (f : ℝ → ℂ) (hf : Continuous f) :
    IntegrableOn (fun t => «prefix» x a t * f t) (Icc 0 D) := by
  classical
  have he : (fun t => «prefix» x a t * f t) =
      fun t => ∑ i, (Ici (x i)).indicator (fun t => a i * f t) t := by
    ext t
    simp only [«prefix», Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x i ≤ t <;> simp [Set.indicator, hi]
  rw [he]
  exact integrable_finsetSum _ (fun i _ =>
    ((continuous_const.mul hf).integrableOn_Icc).indicator measurableSet_Ici)

lemma prefix_memLp (x : I → ℝ) (a : I → ℂ) (D : ℝ)
    (ha : ∑ i, a i = 0) :
    MemLp («prefix» x a) 2 (volume.restrict (Icc 0 D)) := by
  have hi : IntegrableOn («prefix» x a) (Icc 0 D) := by
    simpa only [mul_one] using prefix_mul_integrable x a D (fun _ => 1) continuous_const
  exact (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
    (shifted_hinge_prefix_energy x a ha 0).2.1.integrableOn

/-- Exact integration of a prefix against a continuous multiplier. The upper
cutoff is retained; this is valid without zero mass. -/
private lemma prefix_mul_integral (x : I → ℝ) (a : I → ℂ) (D : ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ t in Icc 0 D, «prefix» x a t * f t) =
      ∑ i, a i * (∫ t in Icc (x i) D, f t) := by
  classical
  have he (t : ℝ) : «prefix» x a t * f t =
      ∑ i, (Ici (x i)).indicator (fun t => a i * f t) t := by
    simp only [«prefix», Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x i ≤ t <;> simp [Set.indicator, hi]
  simp_rw [he]
  rw [integral_finsetSum (f := fun i t =>
    (Ici (x i)).indicator (fun t => a i * f t) t) Finset.univ (fun i _ =>
    ((continuous_const.mul hf).integrableOn_Icc).indicator measurableSet_Ici)]
  apply Finset.sum_congr rfl
  intro i _
  rw [setIntegral_indicator measurableSet_Ici]
  have hs : Icc (0 : ℝ) D ∩ Ici (x i) = Icc (x i) D := by
    ext t
    simp only [mem_inter_iff, mem_Icc, mem_Ici]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨(hx i).1.trans h.1, h.2⟩, h.1⟩⟩
  rw [hs, integral_const_mul]

lemma prefix_moments (x : I → ℝ) (a : I → ℂ) (D : ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (q : ℕ)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    ∀ r : ℕ, r < q → ∫ t in Icc 0 D, (t : ℂ) ^ r * «prefix» x a t = 0 := by
  intro r hr
  have hpow (l : ℝ) (hl : l ≤ D) :
      (∫ t in Icc l D, (t : ℂ) ^ r) =
        (((D : ℂ) ^ (r + 1) - (l : ℂ) ^ (r + 1)) / ((r + 1 : ℕ) : ℂ)) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hl]
    calc
      _ = ((∫ t in l..D, t ^ r : ℝ) : ℂ) := by
        simp only [← Complex.ofReal_pow, intervalIntegral.integral_ofReal]
      _ = _ := by rw [integral_pow]; push_cast; rfl
  calc
    _ = ∫ t in Icc 0 D, «prefix» x a t * (t : ℂ) ^ r := by
      apply integral_congr_ae
      exact ae_of_all _ (fun t => mul_comm _ _)
    _ = ∑ i, a i *
        (((D : ℂ) ^ (r + 1) - (x i : ℂ) ^ (r + 1)) / ((r + 1 : ℕ) : ℂ)) := by
      rw [prefix_mul_integral x a D hx _ (by fun_prop)]
      apply Finset.sum_congr rfl
      intro i _
      rw [hpow (x i) (hx i).2]
    _ = ((∑ i, a i) * (D : ℂ) ^ (r + 1) -
        (∑ i, a i * (x i : ℂ) ^ (r + 1))) / ((r + 1 : ℕ) : ℂ) := by
      simp only [div_eq_mul_inv, sub_mul, mul_sub, Finset.sum_sub_distrib,
        Finset.sum_mul, mul_assoc]
    _ = 0 := by
      have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
      rw [ha, hm (r + 1) (by omega)]
      simp

lemma ramp_continuous (x : I → ℝ) (a : I → ℂ) : Continuous (ramp x a) := by
  unfold ramp
  fun_prop

lemma resolvent_continuous (lam : ℝ) (x : I → ℝ) (a : I → ℂ) :
    Continuous (resolvent lam x a) := by
  unfold resolvent
  fun_prop

lemma second_continuous (lam : ℝ) (x : I → ℝ) (a : I → ℂ) :
    Continuous (secondResolvent lam x a) :=
  ((ramp_continuous x a).sub (resolvent_continuous lam x a)).div_const _

lemma response_eq (lam : ℝ) (hlam : lam ≠ 0)
    (x : I → ℝ) (a : I → ℂ) (t : ℝ) :
    response lam x a t = «prefix» x a t - (lam : ℂ) * resolvent lam x a t := by
  classical
  have hlc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  simp only [response, «prefix», resolvent, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ≤ t
  · rw [ite_eq_left hi, ite_eq_left hi, max_eq_left (sub_nonneg.mpr hi)]
    push_cast
    field_simp [hlam, hlc]
    <;> ring
  · rw [ite_eq_right hi, ite_eq_right hi, max_eq_right (by linarith : t - x i ≤ 0)]
    simp

/-- Right derivatives include atoms at the evaluation point, matching the
inclusive prefix exactly, rather than only almost everywhere. -/
lemma ramp_right (x : I → ℝ) (a : I → ℂ) (t : ℝ) :
    HasDerivWithinAt (ramp x a) («prefix» x a t) (Ioi t) t := by
  classical
  unfold ramp «prefix»
  apply HasDerivWithinAt.fun_sum
  intro i _
  by_cases hi : x i ≤ t
  · have hd : HasDerivWithinAt (fun y : ℝ => a i * ((y - x i : ℝ) : ℂ))
        (a i) (Ioi t) t := by
      simpa using (((hasDerivAt_id t).sub_const (x i)).ofReal_comp.const_mul (a i)).hasDerivWithinAt
        (s := Ioi t)
    have ht : max (t - x i) 0 = t - x i := max_eq_left (sub_nonneg.mpr hi)
    simpa only [ite_eq_left hi, mul_one] using hd.congr
      (fun y hy => by rw [max_eq_left (by linarith [show t < y from hy] : 0 ≤ y - x i)])
      (by rw [ht])
  · have hit : t < x i := lt_of_not_ge hi
    have hd : HasDerivWithinAt (fun _ : ℝ => (0 : ℂ)) 0 (Ioi t) t :=
      (hasDerivAt_const t (0 : ℂ)).hasDerivWithinAt
    simp only [ite_eq_right hi]
    apply hd.congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hit)] with y hy
      rw [max_eq_right (by linarith [show y < x i from hy] : y - x i ≤ 0)]
      simp
    · rw [max_eq_right (by linarith : t - x i ≤ 0)]
      simp

lemma resolvent_right (lam : ℝ) (hlam : lam ≠ 0)
    (x : I → ℝ) (a : I → ℂ) (t : ℝ) :
    HasDerivWithinAt (resolvent lam x a) (response lam x a t) (Ioi t) t := by
  classical
  unfold resolvent response
  apply HasDerivWithinAt.fun_sum
  intro i _
  by_cases hi : x i ≤ t
  · have hd := (((hasDerivAt_const t (1 : ℝ)).sub
        ((((hasDerivAt_id t).sub_const (x i)).const_mul (-lam)).exp)).div_const lam).ofReal_comp.const_mul (a i)
    have hd' : HasDerivWithinAt
        (fun y : ℝ => a i * (((1 - Real.exp (-lam * (y - x i))) / lam : ℝ) : ℂ))
        (a i * (Real.exp (-lam * (t - x i)) : ℂ)) (Ioi t) t := by
      have he : (0 - Real.exp (-lam * (t - x i)) * (-lam * 1)) / lam =
          Real.exp (-lam * (t - x i)) := by field_simp; ring
      simpa only [Pi.sub_apply, id_eq, he] using hd.hasDerivWithinAt (s := Ioi t)
    simp only [ite_eq_left hi]
    exact hd'.congr
      (fun y hy => by rw [max_eq_left (by linarith [show t < y from hy] : 0 ≤ y - x i)])
      (by rw [max_eq_left (sub_nonneg.mpr hi)])
  · have hit : t < x i := lt_of_not_ge hi
    simp only [ite_eq_right hi]
    apply ((hasDerivAt_const t (0 : ℂ)).hasDerivWithinAt).congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hit)] with y hy
      rw [max_eq_right (by linarith [show y < x i from hy] : y - x i ≤ 0)]
      simp
    · rw [max_eq_right (by linarith : t - x i ≤ 0)]
      simp

lemma second_right (lam : ℝ) (hlam : lam ≠ 0)
    (x : I → ℝ) (a : I → ℂ) (t : ℝ) :
    HasDerivWithinAt (secondResolvent lam x a) (resolvent lam x a t) (Ioi t) t := by
  have hlc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  have hd := ((ramp_right x a t).sub (resolvent_right lam hlam x a t)).div_const (lam : ℂ)
  change HasDerivWithinAt (fun y => (ramp x a y - resolvent lam x a y) / (lam : ℂ))
    (resolvent lam x a t) (Ioi t) t
  apply hd.congr_deriv
  rw [response_eq lam hlam]
  field_simp [hlc]
  <;> ring

lemma initial_values (lam : ℝ) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, 0 ≤ x i) :
    ramp x a 0 = 0 ∧ resolvent lam x a 0 = 0 ∧ secondResolvent lam x a 0 = 0 := by
  have hz (i : I) : max (-x i) 0 = 0 := max_eq_right (by linarith [hx i])
  simp [ramp, resolvent, secondResolvent, hz]

lemma ramp_is_primitive (x : I → ℝ) (a : I → ℂ) (D : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hD : 0 ≤ D) :
    ramp x a D = ∫ t in (0 : ℝ)..D, «prefix» x a t := by
  have hf := (prefix_mul_integrable x a D (fun _ => 1) continuous_const)
  simp only [mul_one] at hf
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hD).mpr hf
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hD
    (ramp_continuous x a).continuousOn (fun t _ => ramp_right x a t) hi
  rw [(initial_values 1 x a hx).1, sub_zero] at h
  exact h.symm

lemma ramp_terminal (x : I → ℝ) (a : I → ℂ) (D : ℝ)
    (hx : ∀ i, x i ≤ D) (ha : ∑ i, a i = 0)
    (hfirst : ∑ i, a i * (x i : ℂ) = 0) : ramp x a D = 0 := by
  have he (i : I) : max (D - x i) 0 = D - x i := max_eq_left (sub_nonneg.mpr (hx i))
  simp only [ramp, he, Complex.ofReal_sub,
    mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ha, hfirst]
  ring

private lemma square_right {f : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hd : HasDerivWithinAt f v (Ioi t) t) :
    HasDerivWithinAt (fun y => ‖f y‖ ^ 2)
      (2 * (star (f t) * v).re) (Ioi t) t := by
  have hre : HasDerivWithinAt (fun y => (f y).re) v.re (Ioi t) t := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using!
      Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  have him : HasDerivWithinAt (fun y => (f y).im) v.im (Ioi t) t := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using!
      Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  have hs := (hre.pow 2).add (him.pow 2)
  convert hs using 1
  · ext y
    change ‖f y‖ ^ 2 = (f y).re ^ 2 + (f y).im ^ 2
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  · simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring

lemma square_FTC (D : ℝ) (hD : 0 ≤ D) (f v : ℝ → ℂ)
    (hf : Continuous f) (hd : ∀ t, HasDerivWithinAt f (v t) (Ioi t) t)
    (hi : IntegrableOn (fun t => (star (f t) * v t).re) (Icc 0 D)) :
    ‖f D‖ ^ 2 - ‖f 0‖ ^ 2 =
      2 * (∫ t in Icc 0 D, (star (f t) * v t).re) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hD
    (hf.norm.pow 2).continuousOn (fun t _ => square_right (hd t))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hD).mpr (hi.const_mul 2))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hD,
    ← integral_Icc_eq_integral_Ioc] at h
  exact h.symm

lemma square_sub (z w : ℂ) (r : ℝ) :
    ‖z - (r : ℂ) * w‖ ^ 2 = ‖z‖ ^ 2 -
      2 * r * (star w * z).re + r ^ 2 * ‖w‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

end D5.S3.Analytic.Interpolation.MomentExponentialCoercivity
