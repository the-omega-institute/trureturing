/- GID: D5/S3/Quantum/Petz/DoubleStieltjesMarginals
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Evaluation of the simplex marginal and its identification with the logarithmic boundary density. -/

import D5.S3.Quantum.Petz.DoubleStieltjes

namespace D5.S3.Quantum.Petz.DoubleStieltjesMarginals

open Set MeasureTheory Filter
open D5.S3.Quantum.Petz.DoubleStieltjes
open D5.S3.Quantum.Petz.StieltjesDensity
open D5.S3.Quantum.PositiveResolvent.EulerResolvent

private theorem triangle_to_iterated {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    (∫ p in triangle, f p ∂(volume.prod volume)) =
      ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..(1 - a), f (a, b) := by
  have hi : IntegrableOn f triangle (volume.prod volume) :=
    (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set triangle_subset
  rw [← integral_indicator triangle_isOpen.measurableSet,
    integral_prod _ (hi.integrable_indicator triangle_isOpen.measurableSet)]
  have he (a : ℝ) : (∫ b, triangle.indicator f (a,b)) =
      (Ioo (0 : ℝ) 1).indicator (fun a => ∫ b in Ioo (0 : ℝ) (1-a), f (a,b)) a := by
    by_cases ha : a ∈ Ioo (0 : ℝ) 1
    · rw [indicator_of_mem ha, ← integral_indicator measurableSet_Ioo]
      apply integral_congr_ae
      filter_upwards with b
      have hb : (a,b) ∈ triangle ↔ b ∈ Ioo (0 : ℝ) (1-a) := by
        simp only [triangle, mem_setOf_eq, mem_Ioo]
        constructor
        · intro h
          exact ⟨h.2.1, by linarith [h.2.2]⟩
        · intro h
          exact ⟨ha.1, h.1, by linarith [h.2]⟩
      by_cases h : b ∈ Ioo (0 : ℝ) (1-a)
      · simp only [indicator_of_mem h, indicator_of_mem (hb.mpr h)]
      · simp only [indicator_of_notMem h, indicator_of_notMem (mt hb.mp h)]
    · rw [indicator_of_notMem ha]
      have hn (b : ℝ) : (a,b) ∉ triangle := by
        intro h
        apply ha
        exact ⟨h.1, by have := h.2.1; have := h.2.2; linarith⟩
      simp only [indicator_of_notMem (hn _), integral_zero]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro a ha
  dsimp only
  rw [intervalIntegral.integral_of_le (by linarith [ha.2]), integral_Ioc_eq_integral_Ioo]

private lemma marginal_row {y z : ℝ} (hy : 0 < y) (hz : 0 < z) (hne : y ≠ z)
    (s a : ℝ) :
    (∫ b in (0 : ℝ)..(1-a), aMarginalIntegrand z s y (a,b)) =
      Real.sin (Real.pi*a) *
        (Real.exp (-a * Real.log s + (a-1)*Real.log z) -
         Real.exp (-a * Real.log s + (a-1)*Real.log y)) / Real.log (y/z) := by
  let v := Real.log z - Real.log y
  have hv : v ≠ 0 := sub_ne_zero.mpr (fun h => hne (Real.log_injOn_pos hy hz h.symm))
  let C := -a * Real.log s + (a-1)*Real.log z
  have hd (b : ℝ) : HasDerivAt
      (fun b => Real.sin (Real.pi*a) * Real.exp (C+v*b) / v)
      (aMarginalIntegrand z s y (a,b)) b := by
    have hh := (((Real.hasDerivAt_exp (C+v*b)).comp b
      (((hasDerivAt_id b).const_mul v).const_add C)).const_mul (Real.sin (Real.pi*a))).div_const v
    convert! hh using 1
    dsimp [aMarginalIntegrand, C, v]
    rw [show -a*Real.log s-b*Real.log y+(a+b-1)*Real.log z =
      -a*Real.log s+(a-1)*Real.log z+(Real.log z-Real.log y)*b by ring]
    field_simp [show Real.log z - Real.log y ≠ 0 from hv]
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun b _ => hd b)
    (show IntervalIntegrable (fun b => aMarginalIntegrand z s y (a,b)) volume 0 (1-a) from
      (by unfold aMarginalIntegrand; fun_prop : Continuous _).intervalIntegrable _ _)
  rw [hh, Real.log_div hy.ne' hz.ne']
  have he : C+v*(1-a) = -a*Real.log s+(a-1)*Real.log y := by dsimp [C,v]; ring
  rw [he]
  simp only [mul_zero, add_zero]
  dsimp [C,v]
  have hden : Real.log y - Real.log z ≠ 0 := sub_ne_zero.mpr (fun h => hne (Real.log_injOn_pos hy hz h))
  field_simp [hden, show Real.log z - Real.log y ≠ 0 from hv]
  <;> ring

private lemma marginal_sine_integral {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    (∫ a in (0 : ℝ)..1, Real.sin (Real.pi*a) *
      Real.exp (-a * Real.log s + (a-1)*Real.log u)) =
      Real.pi * (s+u)/(s*u) * E s u := by
  have he : (fun a : ℝ => Real.sin (Real.pi*a) * Real.exp (-a*Real.log s+(a-1)*Real.log u)) =
      fun a => (1/u) * (Real.exp (Real.log (u/s)*a)*Real.sin (Real.pi*a)) := by
    funext a
    rw [Real.log_div hu.ne' hs.ne']
    have hh : -a*Real.log s+(a-1)*Real.log u =
        (Real.log u-Real.log s)*a + -Real.log u := by ring
    rw [hh, Real.exp_add, Real.exp_neg, Real.exp_log hu]
    ring
  rw [he, intervalIntegral.integral_const_mul, integral_exp_sin, Real.exp_log (div_pos hu hs)]
  dsimp [E]
  field_simp
  <;> ring

/-- The normalized simplex marginal is the existing raw density away from coincident nodes. -/
theorem simplex_marginal_eq_rQ {s y z : ℝ} (hs : 0 < s) (hy : 0 < y)
    (hz : 0 < z) (hne : y ≠ z) :
    (1 / Real.pi) * (∫ p in triangle, aMarginalIntegrand z s y p ∂(volume.prod volume)) =
      rQ y z s := by
  rw [triangle_to_iterated (by unfold aMarginalIntegrand; fun_prop)]
  simp_rw [marginal_row hy hz hne s]
  have hi (u : ℝ) : IntervalIntegrable (fun a => Real.sin (Real.pi*a) *
      Real.exp (-a*Real.log s+(a-1)*Real.log u)) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have he : (fun a : ℝ => Real.sin (Real.pi*a) *
      (Real.exp (-a*Real.log s+(a-1)*Real.log z)-Real.exp (-a*Real.log s+(a-1)*Real.log y)) /
      Real.log (y/z)) = fun a =>
      (Real.sin (Real.pi*a)*Real.exp (-a*Real.log s+(a-1)*Real.log z)-
       Real.sin (Real.pi*a)*Real.exp (-a*Real.log s+(a-1)*Real.log y))/Real.log (y/z) := by
    funext a
    ring
  rw [he, intervalIntegral.integral_div, intervalIntegral.integral_sub (hi z) (hi y),
    marginal_sine_integral hs hz, marginal_sine_integral hs hy]
  have hlog (u : ℝ) (hu : 0 < u) : (Real.log (s/u))^2 = (Real.log (u/s))^2 := by
    rw [Real.log_div hs.ne' hu.ne', Real.log_div hu.ne' hs.ne']
    ring
  dsimp [rQ, E]
  rw [hlog z hz, hlog y hy]
  field_simp
  <;> ring

/-- Formula (9), including the integrability of the marginal, at distinct density nodes. -/
theorem A_marginal_eq_rQ {s y z : ℝ} (hs : 0 < s) (hy : 0 < y)
    (hz : 0 < z) (hne : y ≠ z) :
    IntegrableOn (fun t => A z s t / (y+t)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), A z s t / (y+t)) = rQ y z s := by
  have h := A_marginal z s hy
  refine ⟨h.1, ?_⟩
  rw [h.2]
  exact simplex_marginal_eq_rQ hs hy hz hne

/-- The simplex integrand of the canonical logarithmic second divided difference. -/
noncomputable def qIntegrand (x y z : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-p.1 * Real.log x - p.2 * Real.log y + (p.1+p.2-1) * Real.log z)

/-- Source formula (7), obtained by an affine substitution in the canonical square integral. -/
theorem Q_eq_simplex (x y z : ℝ) :
    D5.S3.Quantum.PositiveResolvent.ExponentialSecondDifference.Q x y z =
      ∫ p in triangle, qIntegrand x y z p ∂(volume.prod volume) := by
  rw [triangle_to_iterated (by unfold qIntegrand; fun_prop)]
  have he : (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..(1-a), qIntegrand x y z (a,b)) =
      ∫ s in (0 : ℝ)..1, ∫ b in (0 : ℝ)..s, qIntegrand x y z (1-s,b) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun a : ℝ => ∫ b in (0 : ℝ)..(1-a), qIntegrand x y z (a,b))
      (a := 0) (b := 1) 1
    simp only [sub_self, sub_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [show (1 : ℝ)-(1-s) = s by ring]
  rw [he, D5.S3.Quantum.PositiveResolvent.ExponentialSecondDifference.Q_symm_right x y z]
  unfold D5.S3.Quantum.PositiveResolvent.ExponentialSecondDifference.Q
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun b : ℝ => qIntegrand x y z (1-s,b)) (a := 0) (b := 1) s
  simp only [smul_eq_mul, mul_zero, mul_one] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  unfold qIntegrand
  congr 2
  ring

end D5.S3.Quantum.Petz.DoubleStieltjesMarginals
