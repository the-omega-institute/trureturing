/- GID: D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual patched outer Cauchy integrals and finite-bank integrability. -/

import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCompositionMoments
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Same-witness outer Cauchy control and closed-bank extensions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped ComplexConjugate

namespace D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCircleDefect

/-- The outer coefficient integrand with its single cut point assigned zero. -/
def outerIntegrand (A : ℂ → ℂ) (R : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  if z = (R : ℂ) then 0 else A z / z ^ (n + 1)

/-- The actual positively oriented outer circle contribution. -/
def outerCoefficient (A : ℂ → ℂ) (R : ℝ) (n : ℕ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ * ∮ z in C(0, R), outerIntegrand A R n z

private theorem sphere_omega (R : ℝ) (hR : 0 ≤ R) (z : ℂ)
    (hz : ‖z‖ = R) (hne : z ≠ (R : ℂ)) : z ∈ CompositionContinuation.omega := by
  by_contra ho
  change ¬ (1 - z ∈ Complex.slitPlane) at ho
  rw [Complex.mem_slitPlane_iff] at ho
  push_neg at ho
  have hi : z.im = 0 := by simpa using ho.2
  have hr : 1 ≤ z.re := by simpa only [sub_re, one_re] using (sub_nonpos.mp ho.1)
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
  have hn : ‖z‖ = z.re := by
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] <;> simp
  apply hne
  rw [he, ← hn, hz]

private theorem outer_norm (A : ℂ → ℂ) (R B : ℝ) (hR : 0 < R) (hB : 0 ≤ B)
    (hb : ∀ z ∈ CompositionContinuation.omega, ‖z‖ = R → ‖A z‖ ≤ B)
    (n : ℕ) (z : ℂ) (hz : ‖z‖ = R) :
    ‖outerIntegrand A R n z‖ ≤ B / R ^ (n + 1) := by
  by_cases he : z = (R : ℂ)
  · simp only [outerIntegrand, if_pos he, norm_zero]
    positivity
  · rw [outerIntegrand, if_neg he, norm_div, norm_pow, hz]
    exact div_le_div_of_nonneg_right (hb z (sphere_omega R hR.le z hz he) hz)
      (by positivity)

private theorem outer_integrable (A : ℂ → ℂ) (R0 R B : ℝ)
    (hR : 0 < R) (hRR0 : R < R0) (hB : 0 ≤ B)
    (ha : AnalyticOnNhd ℂ A {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0})
    (hb : ∀ z ∈ CompositionContinuation.omega, ‖z‖ = R → ‖A z‖ ≤ B)
    (n : ℕ) : CircleIntegrable (outerIntegrand A R n) 0 R := by
  let S : Set ℝ := {θ | circleMap 0 R θ ≠ (R : ℂ)}
  have hnorm (θ : ℝ) : ‖circleMap 0 R θ‖ = R := by
    rw [norm_circleMap_zero, abs_of_pos hR]
  have hcA : ContinuousOn (fun θ : ℝ ↦ A (circleMap 0 R θ)) S := by
    apply ha.continuousOn.comp (continuous_circleMap 0 R).continuousOn
    intro θ hθ
    exact ⟨sphere_omega R hR.le _ (hnorm θ) hθ, by rw [hnorm]; exact hRR0⟩
  have hcz : ∀ θ : ℝ, circleMap 0 R θ ≠ 0 := by
    intro θ he
    have := hnorm θ
    rw [he, norm_zero] at this
    linarith
  have hc : ContinuousOn (fun θ : ℝ ↦ outerIntegrand A R n (circleMap 0 R θ)) S := by
    apply (hcA.div ((continuous_circleMap 0 R).continuousOn.pow (n + 1)) (fun θ _ ↦
      pow_ne_zero _ (hcz θ))).congr
    intro θ hθ
    change circleMap 0 R θ ≠ (R : ℂ) at hθ
    simp [outerIntegrand, hθ]
  have hcount : Sᶜ.Countable := by
    simpa only [S, compl_setOf, not_not, preimage, mem_singleton_iff] using
      (countable_singleton (R : ℂ)).preimage_circleMap (0 : ℂ) hR.ne'
  have hm := hc.stronglyMeasurable_of_countable_compl hcount
  change IntervalIntegrable _ volume 0 (2 * Real.pi)
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun θ ↦ outer_norm A R B hR hB hb n _ (hnorm θ))

private theorem outer_bound (A : ℂ → ℂ) (R B : ℝ) (hR : 0 < R) (hB : 0 ≤ B)
    (hb : ∀ z ∈ CompositionContinuation.omega, ‖z‖ = R → ‖A z‖ ≤ B)
    (n : ℕ) : ‖outerCoefficient A R n‖ ≤ B / R ^ n := by
  have hn := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := outerIntegrand A R n) (c := (0 : ℂ)) (C := B / R ^ (n + 1)) hR.le (fun z hz ↦
      outer_norm A R B hR hB hb n z (by simpa [Metric.mem_sphere, dist_zero_right] using hz))
  change ‖outerCoefficient A R n‖ ≤ R * (B / R ^ (n + 1)) at hn
  have heq : R * (B / R ^ (n + 1)) = B / R ^ n := by
    rw [pow_succ]
    field_simp
  rwa [heq] at hn

private theorem bank_integrable (upper : ℂ → ℂ) (ρ R : ℝ)
    (hR : 1 < R) (hRρ : R < 1 + ρ)
    (hu : ContinuousOn upper {z | ‖z - 1‖ ≤ ρ ∧ 0 ≤ z.im}) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ ↦ (upper (x : ℂ)).im / x ^ (n + 1)) volume 1 R := by
  have hc : ContinuousOn (fun x : ℝ ↦ (upper (x : ℂ)).im) (Icc 1 R) := by
    apply Complex.continuous_im.continuousOn.comp' (hu.comp' continuous_ofReal.continuousOn ?_)
      (fun _ _ ↦ mem_univ _)
    intro x hx
    refine ⟨?_, by simp⟩
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - 1)]
    linarith [hx.2]
  have hd := hc.div (continuousOn_id.pow (n + 1)) (fun x hx ↦
    pow_ne_zero (n + 1) (show x ≠ 0 by linarith [hx.1]))
  exact hd.intervalIntegrable_of_Icc hR.le

/-- The continuous upper extension across the finite slit, constructed from the same bank. -/
private def upperExtension (A upper : ℂ → ℂ) (z : ℂ) : ℂ :=
  by classical exact if z ∈ CompositionContinuation.omega then A z else upper z

private theorem upper_extension_continuous (A upper : ℂ → ℂ) (R0 ρ R : ℝ)
    (hR : 1 < R) (hRR0 : R < R0) (hRρ : R < 1 + ρ)
    (ha : ContinuousOn A {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0})
    (hu : ContinuousOn upper {z | ‖z - 1‖ ≤ ρ ∧ 0 ≤ z.im})
    (he : ∀ z, ‖z - 1‖ ≤ ρ → 0 ≤ z.im → z ∈ CompositionContinuation.omega → upper z = A z) :
    ContinuousOn (upperExtension A upper) {z | ‖z‖ ≤ R ∧ 0 ≤ z.im} := by
  classical
  let δ := (ρ + (R - 1)) / 2
  have hδ : R - 1 < δ := by dsimp [δ]; linarith
  have hδρ : δ < ρ := by dsimp [δ]; linarith
  let K : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im ∧ δ ≤ ‖z - 1‖}
  let L : Set ℂ := {z | ‖z‖ ≤ R ∧ 0 ≤ z.im ∧ ‖z - 1‖ ≤ δ}
  have hKO : K ⊆ CompositionContinuation.omega := by
    intro z hz
    by_contra ho
    change ¬ (1 - z ∈ Complex.slitPlane) at ho
    rw [Complex.mem_slitPlane_iff] at ho
    push_neg at ho
    have hi : z.im = 0 := by simpa using ho.2
    have hr : 1 ≤ z.re := by simpa only [sub_re, one_re] using (sub_nonpos.mp ho.1)
    have hez : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    have hn : ‖z‖ = z.re := by
      rw [hez, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] <;> simp
    have hn1 : ‖z - 1‖ = z.re - 1 := by
      rw [hez, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)] <;> simp
    have hz1 := hz.1
    have hz2 := hz.2.2
    rw [hn] at hz1
    rw [hn1] at hz2
    linarith
  have hcK : ContinuousOn (upperExtension A upper) K := by
    apply (ha.mono (fun z hz ↦ ⟨hKO hz, hz.1.trans_lt hRR0⟩)).congr
    intro z hz
    simp only [upperExtension, if_pos (hKO hz)]
  have hcL : ContinuousOn (upperExtension A upper) L := by
    apply (hu.mono (fun z hz ↦ ⟨hz.2.2.trans hδρ.le, hz.2.1⟩)).congr
    intro z hz
    dsimp [upperExtension]
    split_ifs with ho
    · exact (he z (hz.2.2.trans hδρ.le) hz.2.1 ho).symm
    · rfl
  have hK : IsClosed K := (isClosed_le continuous_norm continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le continuous_const (show Continuous (fun z : ℂ ↦ ‖z - 1‖) by fun_prop)))
  have hL : IsClosed L := (isClosed_le continuous_norm continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le (show Continuous (fun z : ℂ ↦ ‖z - 1‖) by fun_prop) continuous_const))
  apply (hcK.union_of_isClosed hcL hK hL).mono
  intro z hz
  by_cases hd : δ ≤ ‖z - 1‖
  · exact Or.inl ⟨hz.1, hz.2, hd⟩
  · exact Or.inr ⟨hz.1, hz.2, (le_of_not_ge hd)⟩

/-- The Jacobian-cancelled pullback to logarithmic coordinates. -/
def upperPullback (P : ℂ → ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  P (Complex.exp w) / (Complex.exp w) ^ n

/-- The oriented boundary identity on the closed upper logarithmic rectangle. -/
def upperRectangleBalance (P : ℂ → ℂ) (R : ℝ) (n : ℕ) : Prop :=
    (∫ x in Real.log (1 / 2 : ℝ)..Real.log R, upperPullback P n (x : ℂ)) -
    (∫ x in Real.log (1 / 2 : ℝ)..Real.log R,
      upperPullback P n ((x : ℂ) + Real.pi * I)) +
    I * (∫ y in (0 : ℝ)..Real.pi, upperPullback P n (Real.log R + y * I)) -
    I * (∫ y in (0 : ℝ)..Real.pi,
      upperPullback P n (Real.log (1 / 2 : ℝ) + y * I)) = 0

private theorem upper_rectangle (A upper : ℂ → ℂ) (R0 ρ R : ℝ)
    (hR : 1 < R) (hRR0 : R < R0) (hRρ : R < 1 + ρ)
    (ha : AnalyticOnNhd ℂ A {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0})
    (hu : ContinuousOn upper {z | ‖z - 1‖ ≤ ρ ∧ 0 ≤ z.im})
    (he : ∀ z, ‖z - 1‖ ≤ ρ → 0 ≤ z.im → z ∈ CompositionContinuation.omega → upper z = A z)
    (n : ℕ) : upperRectangleBalance (upperExtension A upper) R n := by
  classical
  let P := upperExtension A upper
  let f := upperPullback P n
  have hRpos : 0 < R := by linarith
  have hl : Real.log (1 / 2 : ℝ) ≤ Real.log R :=
    Real.log_le_log (by norm_num) (by linarith)
  have hP := upper_extension_continuous A upper R0 ρ R hR hRR0 hRρ
    ha.continuousOn hu he
  have hnorm : ∀ z : ℂ, z.re ≤ Real.log R → ‖Complex.exp z‖ ≤ R := by
    intro z hz
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hz).trans_eq (Real.exp_log hRpos)
  have hc : ContinuousOn f
      (Icc (Real.log (1 / 2 : ℝ)) (Real.log R) ×ℂ Icc 0 Real.pi) := by
    apply (hP.comp' Complex.continuous_exp.continuousOn ?_).div
      (Complex.continuous_exp.continuousOn.pow n) (fun z _ ↦ pow_ne_zero _ (Complex.exp_ne_zero z))
    intro z hz
    refine ⟨hnorm z hz.1.2, ?_⟩
    rw [Complex.exp_im]
    exact mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_mem_Icc hz.2)
  have hd : DifferentiableOn ℂ f
      (Ioo (Real.log (1 / 2 : ℝ)) (Real.log R) ×ℂ Ioo 0 Real.pi) := by
    intro z hz
    have hi : 0 < (Complex.exp z).im := by
      rw [Complex.exp_im]
      exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hz.2.1 hz.2.2)
    have ho : Complex.exp z ∈ CompositionContinuation.omega := by
      change 1 - Complex.exp z ∈ Complex.slitPlane
      rw [Complex.mem_slitPlane_iff]
      right
      simp only [sub_im, one_im, zero_sub, neg_ne_zero]
      exact ne_of_gt hi
    have hpa : AnalyticAt ℂ P (Complex.exp z) := by
      apply (ha _ ⟨ho, (hnorm z hz.1.2.le).trans_lt hRR0⟩).congr
      have hopen : IsOpen CompositionContinuation.omega :=
        Complex.isOpen_slitPlane.preimage (by fun_prop)
      filter_upwards [hopen.mem_nhds ho] with w hw
      simp only [P, upperExtension, if_pos hw]
    exact ((hpa.differentiableAt.comp z Complex.differentiable_exp.differentiableAt).div
      (Complex.differentiable_exp.differentiableAt.pow n)
      (pow_ne_zero _ (Complex.exp_ne_zero z))).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f ⟨Real.log (1 / 2 : ℝ), 0⟩ ⟨Real.log R, Real.pi⟩
    (by simpa only [uIcc_of_le hl, uIcc_of_le Real.pi_pos.le] using hc)
    (by simpa only [min_eq_left hl, max_eq_right hl,
      min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] using hd)
  simpa only [upperRectangleBalance, f, P, Complex.ofReal_zero, zero_mul, add_zero, smul_eq_mul] using h

/-- The literal all-composition outer integral is integrable, and the very same source B
bounds every coefficient error. The finite-slit coefficient identity is a separate obligation. -/
theorem result (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    ∃ R0 ρ R B : ℝ, ∃ upper P : ℂ → ℂ,
      1 < R0 ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < R ∧ R < R0 ∧ R < 1 + ρ ∧ 0 ≤ B ∧
      AnalyticOnNhd ℂ (FiniteSlitCompositionMoments.reciprocal head tail ell)
        {z | z ∈ CompositionContinuation.omega ∧ ‖z‖ < R0} ∧
      (∀ z : ℂ, ‖z‖ < 1 → FiniteSlitCompositionMoments.reciprocal head tail ell z =
        ((CompositionDisk.normalized head tail z)⁻¹) ^ (ell : ℕ)) ∧
      FiniteSlitCompositionMoments.reciprocal head tail ell 0 =
        ((CompositionDisk.normalized head tail 0)⁻¹) ^ (ell : ℕ) ∧
      ContinuousOn upper {z | ‖z - 1‖ ≤ ρ ∧ 0 ≤ z.im} ∧
      (∀ z : ℂ, ‖z - 1‖ ≤ ρ → 0 ≤ z.im → z ∈ CompositionContinuation.omega →
        upper z = FiniteSlitCompositionMoments.reciprocal head tail ell z) ∧
      ContinuousOn P {z | ‖z‖ ≤ R ∧ 0 ≤ z.im} ∧
      (∀ z, ‖z‖ ≤ R → 0 ≤ z.im → z ∈ CompositionContinuation.omega →
        P z = FiniteSlitCompositionMoments.reciprocal head tail ell z) ∧
      (∀ z, ‖z‖ ≤ R → 0 ≤ z.im → z ∉ CompositionContinuation.omega → P z = upper z) ∧
      (∀ z ∈ CompositionContinuation.omega, ‖z‖ = R →
        ‖FiniteSlitCompositionMoments.reciprocal head tail ell z‖ ≤ B) ∧
      (∀ n : ℕ, CircleIntegrable
          (outerIntegrand (FiniteSlitCompositionMoments.reciprocal head tail ell) R n) 0 R ∧
        IntervalIntegrable (fun x : ℝ ↦ (upper (x : ℂ)).im / x ^ (n + 1)) volume 1 R ∧
        ‖outerCoefficient (FiniteSlitCompositionMoments.reciprocal head tail ell) R n‖ ≤ B / R ^ n) ∧
      (∀ n : ℕ, upperRectangleBalance P R n) ∧
      (∀ᶠ n : ℕ in atTop, B / R ^ n + (1 / Real.pi) *
        (∫ x in (1 : ℝ)..R, (upper (x : ℂ)).im / x ^ (n + 1)) < 0) := by
  obtain ⟨R0, ρ, R, upper, hR0, hρ, hρ1, hR, hRR0, hRρ, ha,
    hdisk, hzero, hu, he, _hendpoint, ⟨B, hB, hb⟩, hnegative⟩ :=
      FiniteSlitCompositionMoments.result head tail ell
  refine ⟨R0, ρ, R, B, upper, upperExtension _ upper,
    hR0, hρ, hρ1, hR, hRR0, hRρ, hB, ha, hdisk, hzero, hu, he,
    upper_extension_continuous _ _ _ _ _ hR hRR0 hRρ ha.continuousOn hu he,
    ?_, ?_, hb, ?_, (fun n ↦ upper_rectangle _ _ _ _ _ hR hRR0 hRρ ha hu he n),
    hnegative B⟩
  · intro z _ _ ho
    simp only [upperExtension, if_pos ho]
  · intro z _ _ ho
    simp only [upperExtension, if_neg ho]
  · intro n
    exact ⟨outer_integrable _ R0 R B (by linarith) hRR0 hB ha hb n,
      bank_integrable upper ρ R hR hRρ hu n, outer_bound _ R B (by linarith) hB hb n⟩

end D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitCircleDefect
