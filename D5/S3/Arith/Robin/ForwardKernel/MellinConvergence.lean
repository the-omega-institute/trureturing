/- GID: D5/S3/Arith/Robin/ForwardKernel/MellinConvergence
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MellinConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A power error bound gives absolute convergence of the original forward Mellin integral. -/

import D5.S3.Arith.Robin.ForwardKernel.Transport
import D5.S3.Arith.Robin.OriginalMovingCutAggregate
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

namespace D5.S3.Arith.Robin.ForwardKernel.MellinConvergence

open Set MeasureTheory
open OriginalMovingWindowMoment (width endpoint)
open MellinWeightedVariation (weight)
open ActualVonMangoldtBandCompensation (discrepancy)
open ForwardKernel.Transport (forwardResponse)

noncomputable section

/-- The Lebesgue Mellin integral of the original complete-error response. -/
def forwardMellin (x0 : ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi x0, (forwardResponse x : ℂ) * (x : ℂ) ^ (-s - 1)

private lemma weight_measurable : Measurable weight := by
  unfold weight
  fun_prop

lemma discrepancy_measurable : Measurable discrepancy :=
  Chebyshev.psi_mono.measurable.sub measurable_id

lemma response_measurable : Measurable forwardResponse := by
  have hw : Measurable width := by unfold width; fun_prop
  let f : ℝ × ℝ → ℝ := fun p =>
    (discrepancy (p.1 + p.2) - discrepancy p.1) * (weight (p.1 + p.2) / weight p.1)
  have hf : Measurable f := by
    exact ((discrepancy_measurable.comp (measurable_fst.add measurable_snd)).sub
      (discrepancy_measurable.comp measurable_fst)).mul
        ((weight_measurable.comp (measurable_fst.add measurable_snd)).div
          (weight_measurable.comp measurable_fst))
  let S : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ width p.1}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hw.comp measurable_fst))
  have hI : Measurable (fun x : ℝ => ∫ u : ℝ, S.indicator f (x, u)) :=
    ((hf.indicator hS).stronglyMeasurable.integral_prod_right').measurable
  let S' : Set (ℝ × ℝ) := {p | width p.1 < p.2 ∧ p.2 ≤ 0}
  have hS' : MeasurableSet S' :=
    (measurableSet_lt (hw.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hJ : Measurable (fun x : ℝ => ∫ u : ℝ, S'.indicator f (x, u)) :=
    ((hf.indicator hS').stronglyMeasurable.integral_prod_right').measurable
  have heq (x : ℝ) :
      (∫ u : ℝ, S.indicator f (x, u)) - (∫ u : ℝ, S'.indicator f (x, u)) =
        ∫ u in (0 : ℝ)..width x,
          (discrepancy (x + u) - discrepancy x) * (weight (x + u) / weight x) := by
    unfold intervalIntegral
    rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
    rfl
  have hIJ := hI.sub hJ
  change Measurable (fun x : ℝ =>
    (∫ u : ℝ, S.indicator f (x, u)) - (∫ u : ℝ, S'.indicator f (x, u))) at hIJ
  simp_rw [heq] at hIJ
  exact (Real.continuous_sqrt.measurable.div (hw.pow_const 2)).mul hIJ

/-- An eventual power estimate extends to the fixed half-line by monotonicity of psi. -/
lemma error_power_bound {α : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t → |discrepancy t| ≤ C * t ^ α := by
  obtain ⟨C, t0, hC⟩ := hE
  let B : ℝ := max 2 t0
  let D : ℝ := max |C| (Chebyshev.psi B + B)
  have hD : 0 ≤ D := (abs_nonneg C).trans (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro t ht
  by_cases htail : t0 ≤ t
  · exact (hC t htail).trans (mul_le_mul_of_nonneg_right
      ((le_abs_self C).trans (le_max_left _ _)) (Real.rpow_nonneg (by linarith) _))
  · have htB : t ≤ B := (le_of_not_ge htail).trans (le_max_right _ _)
    calc
      |discrepancy t| ≤ Chebyshev.psi t + t := by
        unfold discrepancy
        exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (Chebyshev.psi_nonneg t),
          abs_of_nonneg (by linarith : 0 ≤ t)])
      _ ≤ Chebyshev.psi B + B := add_le_add (Chebyshev.psi_mono htB) htB
      _ ≤ D := le_max_right _ _
      _ ≤ D * t ^ α := le_mul_of_one_le_right hD (Real.one_le_rpow (by linarith) hα)

/-- A power bound for the Chebyshev error bounds the complete forward increment. -/
theorem forwardResponse_power_bound {C α x : ℝ} (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hE : ∀ t : ℝ, 2 ≤ t → |discrepancy t| ≤ C * t ^ α)
    (hx : 3 ≤ x) :
    |forwardResponse x| ≤
      (2 * C * (2 : ℝ) ^ α) * x ^ (α - 3 / 10) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hwidth : 0 < width x := Real.rpow_pos_of_pos hx0 _
  have hwx : width x ≤ x := by
    unfold width
    exact Real.rpow_le_self_of_one_le hx1 (by norm_num)
  let b : ℝ := α
  let A : ℝ := C * (2 * x) ^ b
  have hb : 0 ≤ b := hα
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hinc (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (width x)) :
      ‖(discrepancy (x + u) - discrepancy x) * (weight (x + u) / weight x)‖ ≤ 2 * A := by
    have hxu : x ≤ x + u := by linarith [hu.1]
    have hxu2 : x + u ≤ 2 * x := by linarith [hu.2]
    have hEx : |discrepancy x| ≤ A := by
      exact (hE x (by linarith)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0.le (by linarith) hb)
          (by positivity))
    have hExu : |discrepancy (x + u)| ≤ A := by
      exact (hE (x + u) (by linarith [hu.1])).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith [hu.1]) hxu2 hb)
          (by positivity))
    have hw : 0 ≤ weight (x + u) / weight x :=
      div_nonneg (MellinWeightedVariation.weight_nonneg (by linarith [hu.1]))
        (MellinWeightedVariation.weight_nonneg (by linarith))
    have hw1 : weight (x + u) / weight x ≤ 1 :=
      (div_le_one (OriginalMovingWindowMoment.weight_pos (by linarith))).2
        (OriginalMovingWindowMoment.weight_antitone (by linarith) hxu)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    have hd := abs_sub (discrepancy (x + u)) (discrepancy x)
    calc
      _ ≤ (2 * A) * (weight (x + u) / weight x) := by gcongr; linarith
      _ ≤ 2 * A := by nlinarith
  have hint := ForwardKernel.Transport.forwardResponse_intervalIntegrable
    (show 1 < x by linarith)
  have hi : ‖∫ u in (0 : ℝ)..width x,
        (discrepancy (x + u) - discrepancy x) * (weight (x + u) / weight x)‖ ≤
      2 * A * width x := by
    calc
      _ ≤ ∫ u in (0 : ℝ)..width x,
          ‖(discrepancy (x + u) - discrepancy x) * (weight (x + u) / weight x)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hwidth.le
      _ ≤ ∫ _u in (0 : ℝ)..width x, 2 * A :=
        intervalIntegral.integral_mono_on hwidth.le hint.norm intervalIntegrable_const hinc
      _ = _ := by simp; ring
  have hfac : 0 ≤ Real.sqrt x / width x ^ 2 := by positivity
  have heq : Real.sqrt x * x ^ b / width x = x ^ (α - 3 / 10) := by
    rw [Real.sqrt_eq_rpow, width, ← Real.rpow_add hx0, ← Real.rpow_sub hx0]
    congr 1
    dsimp [b]
    ring
  change |Real.sqrt x / width x ^ 2 * _| ≤ _
  rw [abs_mul, abs_of_nonneg hfac]
  calc
    _ ≤ (Real.sqrt x / width x ^ 2) * (2 * A * width x) :=
      mul_le_mul_of_nonneg_left hi hfac
    _ = (2 * C * (2 : ℝ) ^ b) *
        (Real.sqrt x * x ^ b / width x) := by
      dsimp [A]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0.le]
      field_simp [hwidth.ne']
      <;> ring
    _ = _ := by rw [heq]

/-- Absolute convergence in the half-plane supplied directly by the pointwise error bound. -/
theorem forwardMellin_integrable {α : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α)
    {x0 : ℝ} (hx0 : 3 ≤ x0) {s : ℂ} (hs : α - 3 / 10 < s.re) :
    IntegrableOn (fun x : ℝ => (forwardResponse x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi x0) := by
  obtain ⟨C, hCp, hC⟩ := error_power_bound hα hE
  let A : ℝ := 2 * C * (2 : ℝ) ^ α
  have hi : IntegrableOn (fun x : ℝ => A * x ^ (α - 3 / 10 - s.re - 1)) (Ioi x0) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)).const_mul A
  have hm : AEStronglyMeasurable
      (fun x : ℝ => (forwardResponse x : ℂ) * (x : ℂ) ^ (-s - 1))
      (volume.restrict (Ioi x0)) := by
    exact ((Complex.measurable_ofReal.comp response_measurable).mul
      (Complex.measurable_ofReal.pow_const (-s - 1))).aestronglyMeasurable
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx3 : 3 ≤ x := hx0.trans hx.le
  have hxpos : 0 < x := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  calc
    _ ≤ (A * x ^ (α - 3 / 10)) * x ^ (-s.re - 1) := by
      gcongr
      exact forwardResponse_power_bound hCp hα hC hx3
    _ = A * x ^ (α - 3 / 10 - s.re - 1) := by
      rw [mul_assoc, ← Real.rpow_add hxpos]
      congr 2
      ring

#print axioms error_power_bound
#print axioms forwardResponse_power_bound
#print axioms forwardMellin_integrable

/-- The original row has exactly its zero-exponent moment as total volume. -/
lemma kernel_volume_eq_moment {x : ℝ} (hx : 4 ≤ x) :
    (∫ t : ℝ, OriginalMovingWindowMoment.kernel x t) =
      OriginalMovingWindowMoment.moment x 0 := by
  have hxb : x ≤ endpoint x := le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _)
  have hs : (∫ t in Ioc x (endpoint x), OriginalMovingWindowMoment.kernel x t) =
      ∫ t : ℝ, OriginalMovingWindowMoment.kernel x t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact if_neg ht
  rw [← hs, ← intervalIntegral.integral_of_le hxb]
  simp [OriginalMovingWindowMoment.moment]

/-- The exact original row volume is an integrable Mellin majorant in the initial half-plane. -/
lemma kernel_mellin_majorant_integrable {x0 : ℝ} (hx0 : 4 ≤ x0) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ (-s - 1)‖ *
      OriginalMovingWindowMoment.moment x 0) (Ici x0) := by
  have hmI : Measurable (fun x : ℝ => ∫ t : ℝ, OriginalMovingWindowMoment.kernel x t) :=
    (OriginalMovingCutAggregate.measurable_kernel_joint.stronglyMeasurable.integral_prod_right').measurable
  have hcp : Measurable (fun x : ℝ => ‖(x : ℂ) ^ (-s - 1)‖) :=
    (Complex.measurable_ofReal.pow_const (-s - 1)).norm
  have hm : AEStronglyMeasurable
      (fun x : ℝ => ‖(x : ℂ) ^ (-s - 1)‖ * OriginalMovingWindowMoment.moment x 0)
      (volume.restrict (Ici x0)) := by
    apply (hcp.mul hmI).aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    change ‖(x : ℂ) ^ (-s - 1)‖ * (∫ t : ℝ, OriginalMovingWindowMoment.kernel x t) =
      ‖(x : ℂ) ^ (-s - 1)‖ * OriginalMovingWindowMoment.moment x 0
    rw [kernel_volume_eq_moment (hx0.trans hx)]
  have hi : IntegrableOn (fun x : ℝ => (5 / 2 : ℝ) * x ^ (-s.re - 1 / 2)) (Ici x0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      ((integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)).const_mul (5 / 2 : ℝ))
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  have hx4 : 4 ≤ x := hx0.trans hx
  have hxpos : 0 < x := by linarith
  have he := OriginalMovingWindowMoment.original_window_moment_estimate hx4
    (show (0 : ℝ) ≤ 0 by norm_num)
  simp only [sub_zero, zero_add, zero_mul, mul_zero, add_zero] at he
  have hε : x ^ (-1 / 5 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith : 1 ≤ x)
      (show (-1 / 5 : ℝ) ≤ 0 by norm_num)
  have hp : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hxpos.le _
  have herror : 4 * x ^ (-1 / 5 : ℝ) * (x ^ (1 / 2 : ℝ) / 2) ≤
      2 * x ^ (1 / 2 : ℝ) := by nlinarith
  have hmoment : |OriginalMovingWindowMoment.moment x 0| ≤ (5 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp he).1, (abs_le.mp he).2]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  calc
    _ ≤ x ^ (-s.re - 1) * ((5 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by
      gcongr
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hxpos]
      congr 2
      ring

#print axioms kernel_mellin_majorant_integrable

end

end D5.S3.Arith.Robin.ForwardKernel.MellinConvergence
