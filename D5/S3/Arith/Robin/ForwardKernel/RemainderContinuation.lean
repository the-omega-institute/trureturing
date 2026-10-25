/- GID: D5/S3/Arith/Robin/ForwardKernel/RemainderContinuation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/RemainderContinuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A power error bound makes the differentiated forward-kernel remainder integrable with zero boundary. -/

import D5.S3.Arith.Robin.ForwardKernel.MellinConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace D5.S3.Arith.Robin.ForwardKernel.RemainderContinuation

open Set MeasureTheory Filter
open scoped Topology
open ActualVonMangoldtBandCompensation (discrepancy)
open ForwardKernel.MellinConvergence (discrepancy_measurable error_power_bound)

noncomputable section

/-- The remainder size and its differentiated size yield both convergence facts
needed at the infinite endpoint of partial summation. -/
theorem remainder_tail_converges
    {α : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α)
    {x0 σ A : ℝ} (hx0 : 3 ≤ x0) (hσ : (α - 7 / 10) < σ) (hA : 0 ≤ A)
    {r dr : ℝ → ℂ}
    (hr : ∀ t : ℝ, x0 ≤ t → ‖r t‖ ≤ A * t ^ (-σ - 7 / 10))
    (hdr : ∀ t : ℝ, x0 ≤ t → ‖dr t‖ ≤ A * t ^ (-σ - 17 / 10))
    (hm : AEStronglyMeasurable dr (volume.restrict (Ioi x0))) :
    IntegrableOn (fun t : ℝ => (discrepancy t : ℂ) * dr t) (Ioi x0) ∧
      Tendsto (fun t : ℝ => (discrepancy t : ℂ) * r t) atTop (𝓝 0) := by
  obtain ⟨C, hCp, hC⟩ := error_power_bound hα hE
  let p : ℝ := α - σ - 7 / 10
  let D : ℝ := C * A
  have hp : p < 0 := by dsimp [p]; linarith
  have hsize {k : ℝ → ℂ} {e : ℝ}
      (hk : ∀ t : ℝ, x0 ≤ t → ‖k t‖ ≤ A * t ^ e)
      (t : ℝ) (ht : x0 ≤ t) :
      ‖(discrepancy t : ℂ) * k t‖ ≤ D * t ^ (α + e) := by
    have ht2 : 2 ≤ t := by linarith
    have ht0 : 0 < t := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (C * t ^ α) * (A * t ^ e) := by
        gcongr
        · exact hC t ht2
        · exact hk t ht
      _ = D * t ^ (α + e) := by
        rw [mul_mul_mul_comm, ← Real.rpow_add ht0]
  constructor
  · have hi : IntegrableOn (fun t : ℝ => D * t ^ (p - 1)) (Ioi x0) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)).const_mul D
    apply hi.mono'
      ((Complex.measurable_ofReal.comp discrepancy_measurable).aestronglyMeasurable.mul hm)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h := hsize hdr t ht.le
    convert h using 1
    congr 2
    dsimp [p]
    ring
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hdecay : Tendsto (fun t : ℝ => D * t ^ p) atTop (𝓝 0) := by
      simpa only [neg_neg, mul_zero] using
        (tendsto_rpow_neg_atTop (neg_pos.mpr hp)).const_mul D
    apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) _ hdecay
    filter_upwards [eventually_ge_atTop x0] with t ht
    have h := hsize hr t ht
    convert h using 1
    congr 2
    dsimp [p]
    ring

#print axioms remainder_tail_converges

/-- Compact bounds on a holomorphic parameter family give a holomorphic
Chebyshev-weighted remainder integral in the enlarged half-plane. -/
theorem remainder_integral_holomorphic
    {α : ℝ} (hα : 0 ≤ α)
    (hE : ∃ C t0 : ℝ, ∀ t : ℝ, t0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ α)
    {x0 : ℝ} (hx0 : 3 ≤ x0) {d : ℂ → ℝ → ℂ}
    (hmeas : ∀ s : ℂ, (α - 7 / 10) < s.re →
      AEStronglyMeasurable (d s) (volume.restrict (Ioi x0)))
    (hhol : ∀ t : ℝ, x0 < t →
      DifferentiableOn ℂ (fun s => d s t) {s : ℂ | (α - 7 / 10) < s.re})
    (hderiv_meas : ∀ s : ℂ, (α - 7 / 10) < s.re →
      AEStronglyMeasurable (fun t => deriv (fun z => d z t) s)
        (volume.restrict (Ioi x0)))
    (hbound : ∀ K : Set ℂ, IsCompact K → K ⊆ {s : ℂ | (α - 7 / 10) < s.re} →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ s ∈ K, ∀ t : ℝ, x0 ≤ t →
        ‖d s t‖ ≤ A * t ^ (-s.re - 17 / 10)) :
    DifferentiableOn ℂ (fun s => ∫ t in Ioi x0, (discrepancy t : ℂ) * d s t)
      {s : ℂ | (α - 7 / 10) < s.re} := by
  intro s hs
  change (α - 7 / 10) < s.re at hs
  let U : Set ℂ := {z : ℂ | (α - 7 / 10) < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  let radius : ℝ := (s.re - α + 7 / 10) / 4
  let σ : ℝ := s.re - 2 * radius
  let K : Set ℂ := Metric.closedBall s (2 * radius)
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hσ : (α - 7 / 10) < σ := by dsimp [σ, radius]; linarith
  have hKre (z : ℂ) (hz : z ∈ K) : σ ≤ z.re := by
    change dist z s ≤ 2 * radius at hz
    rw [dist_eq_norm] at hz
    have hreal : s.re - z.re ≤ ‖z - s‖ := by
      simpa only [Complex.sub_re, norm_sub_rev] using Complex.re_le_norm (s - z)
    dsimp [σ]
    linarith
  have hKU : K ⊆ U := fun z hz => hσ.trans_le (hKre z hz)
  obtain ⟨A, hA, hA_bound⟩ := hbound K (isCompact_closedBall _ _) hKU
  have hterm (z : ℂ) (hz : z ∈ K) (t : ℝ) (ht : x0 ≤ t) :
      ‖d z t‖ ≤ A * t ^ (-σ - 17 / 10) := by
    apply (hA_bound z hz t ht).trans
    apply mul_le_mul_of_nonneg_left _ hA
    exact Real.rpow_le_rpow_of_exponent_le (by linarith)
      (by linarith [hKre z hz])
  have hballK : Metric.ball s radius ⊆ K := by
    intro y hy
    change dist y s ≤ 2 * radius
    have hy' : dist y s < radius := hy
    linarith
  have hclosedK (y : ℂ) (hy : y ∈ Metric.ball s radius) :
      Metric.closedBall y radius ⊆ K := by
    intro z hz
    change dist z s ≤ 2 * radius
    have hz' : dist z y ≤ radius := hz
    have hy' : dist y s < radius := hy
    calc
      dist z s ≤ dist z y + dist y s := dist_triangle _ _ _
      _ ≤ radius + radius := add_le_add hz' hy'.le
      _ = _ := by ring
  have hderiv_bound (y : ℂ) (hy : y ∈ Metric.ball s radius) (t : ℝ) (ht : x0 < t) :
      ‖deriv (fun z => d z t) y‖ ≤ (A / radius) * t ^ (-σ - 17 / 10) := by
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hradius
      ((hhol t ht).diffContOnCl_ball ((hclosedK y hy).trans hKU))
      (fun z hz => hterm z (hclosedK y hy (Metric.sphere_subset_closedBall hz)) t ht.le)
    convert hc using 1
    ring
  have hint (B : ℝ) (hB : 0 ≤ B) (f : ℝ → ℂ)
      (hfm : AEStronglyMeasurable f (volume.restrict (Ioi x0)))
      (hfb : ∀ t : ℝ, x0 ≤ t → ‖f t‖ ≤ B * t ^ (-σ - 17 / 10)) :
      IntegrableOn (fun t : ℝ => (discrepancy t : ℂ) * f t) (Ioi x0) := by
    exact (remainder_tail_converges hα hE hx0 hσ hB
      (r := fun _ => 0) (dr := f)
      (by intro t ht; simp only [norm_zero]; positivity [show 0 ≤ t by linarith]) hfb hfm).1
  let b : ℝ → ℝ := fun t => (A / radius) * t ^ (-σ - 17 / 10)
  let bound : ℝ → ℝ := fun t => ‖(discrepancy t : ℂ)‖ * b t
  have hb (t : ℝ) (ht : x0 ≤ t) : 0 ≤ b t := by
    dsimp [b]
    positivity [show 0 ≤ t by linarith]
  have hbm : AEStronglyMeasurable (fun t => (b t : ℂ))
      (volume.restrict (Ioi x0)) := by
    apply Measurable.aestronglyMeasurable
    dsimp [b]
    fun_prop
  have hbint : IntegrableOn
      (fun t : ℝ => ‖(discrepancy t : ℂ) * (b t : ℂ)‖) (Ioi x0) :=
    (hint (A / radius) (div_nonneg hA hradius.le)
    (fun t => (b t : ℂ)) hbm (by
      intro t ht
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb t ht)])).norm
  have hbound_int : IntegrableOn bound (Ioi x0) := by
    apply hbint.congr_fun _ measurableSet_Ioi
    intro t ht
    change ‖(discrepancy t : ℂ) * (b t : ℂ)‖ = ‖(discrepancy t : ℂ)‖ * b t
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb t ht.le)]
  have hsK : s ∈ K := Metric.mem_closedBall_self (by linarith)
  have hF_int := hint A hA (d s) (hmeas s hs) (hterm s hsK)
  have hF_meas : ∀ᶠ y in 𝓝 s, AEStronglyMeasurable
      (fun t => (discrepancy t : ℂ) * d y t) (volume.restrict (Ioi x0)) := by
    filter_upwards [Metric.ball_mem_nhds s hradius] with y hy
    exact (Complex.measurable_ofReal.comp discrepancy_measurable).aestronglyMeasurable.mul
      (hmeas y (hKU (hballK hy)))
  have hF'_meas : AEStronglyMeasurable
      (fun t => (discrepancy t : ℂ) * deriv (fun z => d z t) s)
      (volume.restrict (Ioi x0)) :=
    (Complex.measurable_ofReal.comp discrepancy_measurable).aestronglyMeasurable.mul
      (hderiv_meas s hs)
  have hbd : ∀ᵐ t : ℝ ∂volume.restrict (Ioi x0), ∀ y ∈ Metric.ball s radius,
      ‖(discrepancy t : ℂ) * deriv (fun z => d z t) y‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hderiv_bound y hy t ht) (norm_nonneg _)
  have hdiff : ∀ᵐ t : ℝ ∂volume.restrict (Ioi x0), ∀ y ∈ Metric.ball s radius,
      HasDerivAt (fun z => (discrepancy t : ℂ) * d z t)
        ((discrepancy t : ℂ) * deriv (fun z => d z t) y) y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y hy
    exact (((hhol t ht).differentiableAt
      (hU.mem_nhds (hKU (hballK hy)))).hasDerivAt).const_mul _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y t => (discrepancy t : ℂ) * d y t)
    (F' := fun y t => (discrepancy t : ℂ) * deriv (fun z => d z t) y)
    (bound := bound) (Metric.ball_mem_nhds s hradius) hF_meas hF_int hF'_meas
    hbd hbound_int hdiff).2.differentiableAt.differentiableWithinAt

#print axioms remainder_integral_holomorphic

end

end D5.S3.Arith.Robin.ForwardKernel.RemainderContinuation
