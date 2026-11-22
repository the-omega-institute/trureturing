/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterCollisionRadicand
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive integral regularization of the radicand at coincident upper roots. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailAverage
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailFormula
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # A positive integral for the repeated-node radicand -/

open Set MeasureTheory

namespace RefinedBMV.PositiveCenter

/-- The exponential gap divided by its argument, continued through zero. -/
noncomputable def expGapMean (h t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, Real.exp (-(h*t*s))

@[fun_prop] theorem expGapMean_continuous :
    Continuous (fun z : ℝ × ℝ ↦ expGapMean z.1 z.2) := by
  unfold expGapMean
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) _ _

private noncomputable def collisionInner (h t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, s * Real.exp (-(h*t*s)) * expGapMean 1 (t*s)

@[fun_prop] private theorem collisionInner_continuous :
    Continuous (fun z : ℝ × ℝ ↦ collisionInner z.1 z.2) := by
  unfold collisionInner
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := 0) (b₀ := 1)
  fun_prop

/-- Continuous normalization of the radicand by its fourth-order zero. -/
noncomputable def collisionRadicand (h t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, s^3 * Real.exp (-(2*t*s)) * expGapMean h (t*s) *
    collisionInner h (t*s)

theorem collisionRadicand_continuous :
    Continuous (fun z : ℝ × ℝ ↦ collisionRadicand z.1 z.2) := by
  unfold collisionRadicand
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := 0) (b₀ := 1)
  fun_prop

private theorem scale_unit_integral (f : ℝ → ℝ) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, f s) = t * ∫ s in (0 : ℝ)..1, f (t*s) := by
  simpa only [mul_zero, mul_one, smul_eq_mul] using
    (intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) f t).symm

theorem expGapMean_eq {h : ℝ} (hh : 0 < h) (t : ℝ) :
    upperTailGap h t = t * expGapMean h t := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hasDerivAt_upperTailGap (t := s) hh)
    (Continuous.intervalIntegrable (by fun_prop) 0 t)
  have hzero : upperTailGap h 0 = 0 := by simp [upperTailGap]
  rw [hzero, sub_zero, scale_unit_integral] at hi
  simpa only [expGapMean, mul_assoc] using hi.symm

private theorem collisionInner_eq {h : ℝ} (hh : 0 < h) (t : ℝ) :
    (1+h)*upperTailGap h t - 1 + Real.exp (-((1+h)*t)) =
      (1+h)*t^2*collisionInner h t := by
  let j : ℝ := 1+h
  let H : ℝ → ℝ := fun s ↦ j*upperTailGap h s - 1 + Real.exp (-(j*s))
  have hj : 0 < j := by dsimp [j]; positivity
  have hD (s : ℝ) : HasDerivAt H (j*(Real.exp (-(h*s))-Real.exp (-(j*s)))) s := by
    have hfac : HasDerivAt (fun x : ℝ ↦ -(j*x)) (-j) s := by
      have hl := (hasDerivAt_id' s).const_mul j
      have hd := hl.neg
      change HasDerivAt (fun x : ℝ ↦ -(j*x)) (-(j*1)) s at hd
      simpa only [mul_one] using hd
    have he := hfac.exp
    have hd := (((hasDerivAt_upperTailGap (t := s) hh).const_mul j).sub_const 1).add he
    refine hd.congr_deriv ?_
    ring
  have hzero : H 0 = 0 := by simp [H, upperTailGap]
  calc
    _ = H t := rfl
    _ = ∫ s in (0 : ℝ)..t, j*(Real.exp (-(h*s))-Real.exp (-(j*s))) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hD s)
        (Continuous.intervalIntegrable (by fun_prop) _ _), hzero, sub_zero]
    _ = (1+h)*t^2*collisionInner h t := by
      rw [scale_unit_integral]
      unfold collisionInner
      change t*(∫ s in (0 : ℝ)..1, j*(Real.exp (-(h*(t*s)))-Real.exp (-(j*(t*s))))) =
        j*t^2*(∫ s in (0 : ℝ)..1, s*Real.exp (-(h*t*s))*expGapMean 1 (t*s))
      rw [show j*t^2 = t*(j*t) by ring, mul_assoc]
      simp only [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      have hgap : (t*s)*expGapMean 1 (t*s) = 1-Real.exp (-(t*s)) := by
        rw [← expGapMean_eq (by norm_num : (0 : ℝ) < 1)]
        simp [upperTailGap]
      have he : Real.exp (-(j*(t*s))) =
          Real.exp (-(h*(t*s)))*Real.exp (-(t*s)) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [j]
        ring
      rw [he]
      rw [show -(h*(t*s)) = -(h*t*s) by ring]
      calc
        _ = t*j*Real.exp (-(h*t*s))*(1-Real.exp (-(t*s))) := by ring
        _ = _ := by rw [← hgap]; ring

theorem one_sub_upperTailLambda_eq_collisionRadicand {h : ℝ} (hh : 0 < h) (t : ℝ) :
    1-upperTailLambda h t = (3+h)*(3+2*h)*(1+h)*t^4*collisionRadicand h t := by
  let X : ℝ → ℝ := fun s ↦ 1-upperTailLambda h s
  let g : ℝ := 3+h
  let k : ℝ := 3+2*h
  let j : ℝ := 1+h
  let H : ℝ → ℝ := fun s ↦ j*upperTailGap h s-1+Real.exp (-(j*s))
  have hD (s : ℝ) : HasDerivAt X (g*k*Real.exp (-(2*s))*upperTailGap h s*H s) s := by
    have h := (hasDerivAt_const s (1 : ℝ)).fun_sub (hasDerivAt_upperTailLambda hh)
    change HasDerivAt X _ s at h
    exact h.congr_deriv (by dsimp [g, k, H, j]; ring)
  have hzero : X 0 = 0 := by simp [X, upperTailLambda, upperTailGap]
  have hcont : Continuous (fun s ↦ g*k*Real.exp (-(2*s))*upperTailGap h s*H s) := by
    unfold H upperTailGap
    fun_prop
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hD s)
    (hcont.intervalIntegrable 0 t)
  rw [hzero, sub_zero, scale_unit_integral] at hInt
  change X t = g*k*j*t^4*collisionRadicand h t
  rw [← hInt, show g*k*j*t^4 = t*(g*k*j*t^3) by ring]
  unfold collisionRadicand
  rw [mul_assoc]
  simp only [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [expGapMean_eq hh, show H (t*s) = j*(t*s)^2*collisionInner h (t*s)
      from collisionInner_eq hh (t*s)]
  rw [show -(2*(t*s)) = -(2*t*s) by ring]
  ring

theorem expGapMean_pos (h t : ℝ) : 0 < expGapMean h t := by
  unfold expGapMean
  apply intervalIntegral.integral_pos zero_lt_one (Continuous.continuousOn (by fun_prop))
  · exact fun s _ ↦ (Real.exp_pos _).le
  · exact ⟨1, right_mem_Icc.mpr zero_le_one, Real.exp_pos _⟩

private theorem collisionInner_pos (h t : ℝ) : 0 < collisionInner h t := by
  unfold collisionInner
  apply intervalIntegral.integral_pos zero_lt_one (Continuous.continuousOn (by fun_prop))
  · exact fun s hs ↦ mul_nonneg (mul_nonneg hs.1.le (Real.exp_pos _).le) (expGapMean_pos _ _).le
  · exact ⟨1, right_mem_Icc.mpr zero_le_one,
      mul_pos (mul_pos zero_lt_one (Real.exp_pos _)) (expGapMean_pos _ _)⟩

/-- The regularized radicand is positive even at the collision. -/
theorem collisionRadicand_pos (h t : ℝ) : 0 < collisionRadicand h t := by
  unfold collisionRadicand
  apply intervalIntegral.integral_pos zero_lt_one (Continuous.continuousOn (by fun_prop))
  · intro s hs
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hs.1.le _) (Real.exp_pos _).le)
      (expGapMean_pos _ _).le) (collisionInner_pos _ _).le
  · exact ⟨1, right_mem_Icc.mpr zero_le_one,
      mul_pos (mul_pos (mul_pos (pow_pos zero_lt_one _) (Real.exp_pos _))
        (expGapMean_pos _ _)) (collisionInner_pos _ _)⟩

/-- The exponential integral decreases as either nonnegative parameter increases. -/
theorem expGapMean_antitone {h h' t t' : ℝ} (hh₀ : 0 ≤ h) (hh : h ≤ h')
    (ht₀ : 0 ≤ t) (ht : t ≤ t') : expGapMean h' t' ≤ expGapMean h t := by
  unfold expGapMean
  apply intervalIntegral.integral_mono_on zero_le_one
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro s hs
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right
    (mul_le_mul hh ht ht₀ (hh₀.trans hh)) hs.1))

private theorem collisionInner_antitone {h h' t t' : ℝ} (hh₀ : 0 ≤ h) (hh : h ≤ h')
    (ht₀ : 0 ≤ t) (ht : t ≤ t') : collisionInner h' t' ≤ collisionInner h t := by
  unfold collisionInner
  apply intervalIntegral.integral_mono_on zero_le_one
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro s hs
  have hE : Real.exp (-(h'*t'*s)) ≤ Real.exp (-(h*t*s)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul hh ht ht₀ (hh₀.trans hh)) hs.1))
  have hG := expGapMean_antitone (h := 1) (h' := 1) zero_le_one le_rfl
    (mul_nonneg ht₀ hs.1) (mul_le_mul_of_nonneg_right ht hs.1)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hE hs.1) hG (expGapMean_pos _ _).le
    (mul_nonneg hs.1 (Real.exp_pos _).le)

/-- Both gap and degree parameter can be enclosed by their monotone endpoints. -/
theorem collisionRadicand_antitone {h h' t t' : ℝ} (hh₀ : 0 ≤ h) (hh : h ≤ h')
    (ht₀ : 0 ≤ t) (ht : t ≤ t') : collisionRadicand h' t' ≤ collisionRadicand h t := by
  unfold collisionRadicand
  apply intervalIntegral.integral_mono_on zero_le_one
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro s hs
  have hE : Real.exp (-(2*t'*s)) ≤ Real.exp (-(2*t*s)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ht (by norm_num)) hs.1))
  have hts := mul_le_mul_of_nonneg_right ht hs.1
  have hts₀ := mul_nonneg ht₀ hs.1
  have hA := expGapMean_antitone hh₀ hh hts₀ hts
  have hI := collisionInner_antitone hh₀ hh hts₀ hts
  have he₀ : 0 ≤ s^3*Real.exp (-(2*t*s)) := mul_nonneg (pow_nonneg hs.1 _) (Real.exp_pos _).le
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hE (pow_nonneg hs.1 _)) hA
    (expGapMean_pos _ _).le he₀) hI (collisionInner_pos _ _).le
    (mul_nonneg he₀ (expGapMean_pos _ _).le)

/-- The second regularized defect is the reflection of the first one
after shifting the exponential rates. -/
noncomputable def collisionWeight (h t : ℝ) : ℝ :=
  Real.exp (-((3+2*h)*t)) * collisionRadicand h (-t)

theorem collisionWeight_pos (h t : ℝ) : 0 < collisionWeight h t :=
  mul_pos (Real.exp_pos _) (collisionRadicand_pos _ _)

theorem collisionWeight_continuous :
    Continuous (fun z : ℝ × ℝ ↦ collisionWeight z.1 z.2) := by
  unfold collisionWeight
  exact (by fun_prop : Continuous fun z : ℝ × ℝ ↦ Real.exp (-((3+2*z.1)*z.2))).mul
    (collisionRadicand_continuous.comp (continuous_fst.prodMk continuous_snd.neg))

theorem collisionWeight_eq {h : ℝ} (hh : 0 < h) (t : ℝ) :
    Real.exp (-((3+2*h)*t)) - 1 + (3+2*h)*upperTailGap h t -
      ((3+h)*(3+2*h)/2)*(upperTailGap h t)^2*Real.exp (-t) =
      (3+h)*(3+2*h)*(1+h)*t^4*collisionWeight h t := by
  let a := upperTailGap h t
  let k : ℝ := 3+2*h
  let g : ℝ := 3+h
  let c : ℝ := g*k/2
  let j : ℝ := 1+h
  let E := Real.exp (-(k*t))
  let F := Real.exp (h*t)
  let G := Real.exp (g*t)
  let H := Real.exp (2*t)
  let P := Real.exp (-(h*t))
  have hP : P = 1-h*a := by
    unfold P a upperTailGap
    field_simp [hh.ne']
    ring
  have hPF : P*F = 1 := by
    unfold P F
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have ha : upperTailGap h (-t) = -F*a := by
    change (1 - Real.exp (-(h*(-t)))) / h = -F*a
    rw [show -(h*(-t)) = h*t by ring]
    apply (div_eq_iff hh.ne').2
    calc
      1-F = P*F-F := by rw [hPF]
      _ = _ := by rw [hP]; ring
  have hEG : E*G = P := by
    unfold E G P
    rw [← Real.exp_add]
    dsimp [k, g]
    congr 1
    ring
  have hEFH : E*F^2*H = Real.exp (-t) := by
    unfold E F H
    rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    dsimp [k]
    congr 1
    ring
  have hX := one_sub_upperTailLambda_eq_collisionRadicand hh (-t)
  rw [show (-t)^4 = t^4 by ring] at hX
  change E - 1 + k*a - c*a^2*Real.exp (-t) = g*k*j*t^4*(E*collisionRadicand h (-t))
  calc
    _ = E - P + g*a - c*a^2*Real.exp (-t) := by
      rw [hP]
      dsimp [g, k]
      ring
    _ = E - E*G + (E*G)*(F*a)*g - c*a^2*(E*F^2*H) := by
      rw [hEG, hEFH, ← mul_assoc P F a, hPF, one_mul]
      ring
    _ = E*(1-upperTailLambda h (-t)) := by
      unfold upperTailLambda
      rw [ha, show -((3+h)*(-t)) = g*t by dsimp [g]; ring,
        show -(2*(-t)) = 2*t by ring]
      change _ = E*(1 - ((1 + g*(-F*a))*G + c*(-F*a)^2*H))
      ring
    _ = _ := by rw [hX]; ring

private noncomputable def reflectedMean (h t x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, Real.exp (-(h*t*(1-x*s)))

@[fun_prop] private theorem reflectedMean_continuous :
    Continuous (fun z : ℝ × ℝ × ℝ ↦ reflectedMean z.1 z.2.1 z.2.2) := by
  unfold reflectedMean
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := 0) (b₀ := 1)
  fun_prop

private theorem reflectedMean_eq (h t x : ℝ) :
    Real.exp (-(h*t)) * expGapMean h (-(t*x)) = reflectedMean h t x := by
  unfold reflectedMean expGapMean
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [← Real.exp_add]
  congr 1
  ring

private theorem reflectedMean_pos (h t x : ℝ) : 0 < reflectedMean h t x := by
  rw [← reflectedMean_eq]
  exact mul_pos (Real.exp_pos _) (expGapMean_pos _ _)

private theorem reflectedMean_antitone {h h' t t' x : ℝ} (hh₀ : 0 ≤ h)
    (hh : h ≤ h') (ht₀ : 0 ≤ t) (ht : t ≤ t') (hx : x ≤ 1) :
    reflectedMean h' t' x ≤ reflectedMean h t x := by
  unfold reflectedMean
  apply intervalIntegral.integral_mono_on zero_le_one
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro s hs
  have hxs : x*s ≤ 1 := (mul_le_mul_of_nonneg_right hx hs.1).trans (by simpa using hs.2)
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right
    (mul_le_mul hh ht ht₀ (hh₀.trans hh)) (sub_nonneg.mpr hxs)))

private noncomputable def reflectedInner (h t x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, y * Real.exp (-(h*t*(1-x*y))) * reflectedMean 1 t (x*y)

@[fun_prop] private theorem reflectedInner_continuous :
    Continuous (fun z : ℝ × ℝ × ℝ ↦ reflectedInner z.1 z.2.1 z.2.2) := by
  unfold reflectedInner
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := 0) (b₀ := 1)
  fun_prop

private theorem reflectedInner_eq (h t x : ℝ) :
    Real.exp (-((1+h)*t)) * collisionInner h (-(t*x)) = reflectedInner h t x := by
  unfold reflectedInner collisionInner
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  rw [← reflectedMean_eq, show -(t*(x*y)) = -(t*x)*y by ring]
  rw [show Real.exp (-(h*t*(1-x*y))) = Real.exp (-(h*t)) *
      Real.exp (-(h* (-(t*x))*y)) by rw [← Real.exp_add]; congr 1; ring]
  rw [show Real.exp (-((1+h)*t)) = Real.exp (-(h*t))*Real.exp (-(1*t)) by
    rw [← Real.exp_add]; congr 1; ring]
  ring

private theorem reflectedInner_pos (h t x : ℝ) : 0 < reflectedInner h t x := by
  rw [← reflectedInner_eq]
  exact mul_pos (Real.exp_pos _) (collisionInner_pos _ _)

private theorem reflectedInner_antitone {h h' t t' x : ℝ} (hh₀ : 0 ≤ h)
    (hh : h ≤ h') (ht₀ : 0 ≤ t) (ht : t ≤ t') (hx : x ≤ 1) :
    reflectedInner h' t' x ≤ reflectedInner h t x := by
  unfold reflectedInner
  apply intervalIntegral.integral_mono_on zero_le_one
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro y hy
  have hxy : x*y ≤ 1 := (mul_le_mul_of_nonneg_right hx hy.1).trans (by simpa using hy.2)
  have hE := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right
    (mul_le_mul hh ht ht₀ (hh₀.trans hh)) (sub_nonneg.mpr hxy)))
  exact mul_le_mul (mul_le_mul_of_nonneg_left hE hy.1)
    (reflectedMean_antitone zero_le_one le_rfl ht₀ ht hxy) (reflectedMean_pos _ _ _).le
    (mul_nonneg hy.1 (Real.exp_pos _).le)

private theorem collisionWeight_integral (h t : ℝ) :
    collisionWeight h t = ∫ x in (0 : ℝ)..1, x^3 * Real.exp (-(2*(1-x)*t)) *
      reflectedMean h t x * reflectedInner h t x := by
  unfold collisionWeight collisionRadicand
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [← reflectedMean_eq, ← reflectedInner_eq, show -(2*(-t)*x) = 2*t*x by ring]
  simp only [neg_mul]
  have hE : Real.exp (-(3+2*h)*t) * Real.exp (2*t*x) =
      Real.exp (-(2*(1-x))*t)*Real.exp (-h*t)*Real.exp (-(1+h)*t) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-(3+2*h)*t) * Real.exp (2*t*x)) *
        (x^3 * expGapMean h (-t*x) * collisionInner h (-t*x)) := by ring
    _ = _ := by rw [hE]; ring

/-- The reflected normalized defect also decreases in the gap and degree parameter. -/
theorem collisionWeight_antitone {h h' t t' : ℝ} (hh₀ : 0 ≤ h) (hh : h ≤ h')
    (ht₀ : 0 ≤ t) (ht : t ≤ t') : collisionWeight h' t' ≤ collisionWeight h t := by
  rw [collisionWeight_integral, collisionWeight_integral]
  apply intervalIntegral.integral_mono_on zero_le_one
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro x hx
  have hE : Real.exp (-(2*(1-x)*t')) ≤ Real.exp (-(2*(1-x)*t)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left ht
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hx.2))))
  have h₀ : 0 ≤ x^3*Real.exp (-(2*(1-x)*t)) := mul_nonneg (pow_nonneg hx.1 _) (Real.exp_pos _).le
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hE (pow_nonneg hx.1 _))
    (reflectedMean_antitone hh₀ hh ht₀ ht hx.2) (reflectedMean_pos _ _ _).le h₀)
    (reflectedInner_antitone hh₀ hh ht₀ ht hx.2) (reflectedInner_pos _ _ _).le
    (mul_nonneg h₀ (reflectedMean_pos _ _ _).le)

/-- The repeated-root correction with its quadratic zero divided out. -/
noncomputable def collisionRepeatDefect (h t : ℝ) : ℝ :=
  (3+h)*(3+2*h) * ∫ x in (0 : ℝ)..1,
    x * Real.exp (-((3+h)*t*x)) * expGapMean h (t*x)

@[fun_prop] theorem collisionRepeatDefect_continuous :
    Continuous (fun z : ℝ × ℝ ↦ collisionRepeatDefect z.1 z.2) := by
  unfold collisionRepeatDefect
  apply Continuous.mul (by fun_prop)
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := 0) (b₀ := 1)
  fun_prop

theorem one_sub_upperTailRepeatCorrection_eq_collisionRepeatDefect {h : ℝ}
    (hh : 0 < h) (t : ℝ) :
    1-upperTailRepeatCorrection h t = t^2 * collisionRepeatDefect h t := by
  let g : ℝ := 3+h
  let k : ℝ := 3+2*h
  let Y : ℝ → ℝ := fun s ↦ 1-upperTailRepeatCorrection h s
  have hD (s : ℝ) :
      HasDerivAt Y (g*k*Real.exp (-(g*s))*upperTailGap h s) s := by
    have hlin : HasDerivAt (fun x : ℝ ↦ -(g*x)) (-g) s := by
      have hneg := ((hasDerivAt_id' s).const_mul g).neg
      change HasDerivAt (fun x : ℝ ↦ -(g*x)) (-(g*1)) s at hneg
      simpa only [mul_one] using hneg
    have hgap : Real.exp (-(h*s)) = 1-h*upperTailGap h s := by
      unfold upperTailGap
      field_simp [hh.ne']
      ring
    have hprod := (((hasDerivAt_upperTailGap (t := s) hh).const_mul g).const_add 1).mul hlin.exp
    have hsub := (hasDerivAt_const s (1 : ℝ)).fun_sub hprod
    change HasDerivAt Y _ s at hsub
    refine hsub.congr_deriv ?_
    rw [hgap]
    dsimp [g, k]
    ring
  have hzero : Y 0 = 0 := by simp [Y, upperTailRepeatCorrection, upperTailGap]
  have hcontinuous : Continuous (fun s ↦ g*k*Real.exp (-(g*s))*upperTailGap h s) := by
    unfold upperTailGap
    fun_prop
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hD s)
    (hcontinuous.intervalIntegrable 0 t)
  rw [hzero, sub_zero, scale_unit_integral] at hInt
  change Y t = _
  rw [← hInt]
  unfold collisionRepeatDefect
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [expGapMean_eq hh, show -(g*(t*x)) = -((3+h)*t*x) by dsimp [g]; ring]
  dsimp [g, k]
  ring

#print axioms one_sub_upperTailLambda_eq_collisionRadicand
#print axioms collisionRadicand_pos
#print axioms collisionRadicand_antitone
#print axioms collisionWeight_eq
#print axioms collisionWeight_antitone
#print axioms one_sub_upperTailRepeatCorrection_eq_collisionRepeatDefect

end RefinedBMV.PositiveCenter
