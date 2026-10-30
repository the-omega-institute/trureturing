/- GID: D5/S3/Analytic/Interpolation/SchurBoundaryKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/SchurBoundaryKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Group.FunctionSeries, mathlib/module/Mathlib.Analysis.PSeries, mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence, mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic]
   utility: none
   digest: The real Fourier kernel for an imaginary-axis divided difference. -/

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Poisson

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Analytic.Interpolation.SchurBoundaryKernel

/-- The actual odd cosine series of the imaginary-axis primitive average. -/
def boundaryTerm (b θ : ℝ) (j : ℕ) : ℝ :=
  2 * ((-1 : ℝ) ^ (j + 1) * b ^ (2 * j + 2)) /
    ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3)) * Real.cos ((2 * (j : ℝ) + 1) * θ)

def boundaryKernel (b θ : ℝ) : ℝ := ∑' j : ℕ, boundaryTerm b θ j

private def majorant (j : ℕ) : ℝ :=
  2 / ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3))

private theorem majorant_summable : Summable majorant := by
  have hs : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  apply Summable.of_nonneg_of_le (fun j => by dsimp [majorant]; positivity) _ hs
  intro j
  dsimp [majorant]
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

private theorem term_norm_le {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (θ : ℝ) (j : ℕ) :
    ‖boundaryTerm b θ j‖ ≤ majorant j := by
  have hp : |b ^ (2 * j + 2)| ≤ 1 := by
    rw [abs_pow, abs_of_nonneg hb.1]
    exact pow_le_one₀ hb.1 hb.2
  have hc := Real.abs_cos_le_one ((2 * (j : ℝ) + 1) * θ)
  rw [Real.norm_eq_abs]
  dsimp [boundaryTerm, majorant]
  rw [abs_mul, abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : 0 < (2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3))]
  calc
    _ ≤ (2 * 1 / ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3))) * 1 :=
      mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num))
        (by positivity)) hc (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem term_summable {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    Summable (boundaryTerm b θ) :=
  (majorant_summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_norm_le hb θ)).of_norm

private theorem kernel_continuous {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    Continuous (boundaryKernel b) := by
  exact continuous_tsum (fun j => by unfold boundaryTerm; fun_prop)
    majorant_summable (fun j θ => term_norm_le hb θ j)

private theorem kernel_uniform_convergence :
    TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => ∑ j ∈ Finset.range n, boundaryTerm p.1 p.2 j)
      (fun p => boundaryKernel p.1 p.2) atTop {p | p.1 ∈ Icc (0 : ℝ) 1} :=
  tendstoUniformlyOn_tsum_nat majorant_summable (fun j p hp => term_norm_le hp p.2 j)

private theorem kernel_reflection (b θ : ℝ) :
    boundaryKernel b (Real.pi - θ) = -boundaryKernel b θ := by
  unfold boundaryKernel
  rw [← tsum_neg]
  apply tsum_congr
  intro j
  have hc : Real.cos ((2 * (j : ℝ) + 1) * (Real.pi - θ)) =
      -Real.cos ((2 * (j : ℝ) + 1) * θ) := by
    have he : (2 * (j : ℝ) + 1) * (Real.pi - θ) =
        ((2 * j + 1 : ℕ) : ℝ) * Real.pi - (2 * (j : ℝ) + 1) * θ := by push_cast; ring
    rw [he, Real.cos_nat_mul_pi_sub]
    norm_num [pow_add, pow_mul]
  simp only [boundaryTerm, hc, mul_neg]

private theorem cosine_geometric (q θ : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun j : ℕ => (-q) ^ j * Real.cos ((2 * (j : ℝ) + 1) * θ))
      (Real.cos θ * (1 + q) / ((1 - q) ^ 2 + 4 * q * (Real.cos θ) ^ 2)) := by
  let u : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hr : ‖-(q : ℂ) * u ^ 2‖ < 1 := by
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0,
      norm_pow, hu, one_pow, mul_one]
    exact hq1
  have hh := Complex.reCLM.hasSum
    ((hasSum_geometric_of_norm_lt_one hr).mul_left u)
  have he (j : ℕ) :
      (u * (-(q : ℂ) * u ^ 2) ^ j).re =
        (-q) ^ j * Real.cos ((2 * (j : ℝ) + 1) * θ) := by
    have hp : u * (-(q : ℂ) * u ^ 2) ^ j = (-q : ℂ) ^ j * u ^ (2 * j + 1) := by
      rw [mul_pow, ← pow_mul, pow_succ]
      ring
    have hex : (u ^ (2 * j + 1)).re = Real.cos ((2 * (j : ℝ) + 1) * θ) := by
      rw [show u ^ (2 * j + 1) =
        Complex.exp ((((2 * j + 1 : ℕ) : ℂ) * θ) * Complex.I) by
          rw [mul_assoc, Complex.exp_nat_mul]]
      simpa using
          Complex.exp_ofReal_mul_I_re ((2 * (j : ℝ) + 1) * θ)
    rw [hp]
    simpa only [← Complex.ofReal_neg, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      congrArg (fun x : ℝ => (-q) ^ j * x) hex
  change HasSum (fun j : ℕ => (u * (-(q : ℂ) * u ^ 2) ^ j).re)
    ((u * (1 - (-(q : ℂ) * u ^ 2))⁻¹).re) at hh
  simp_rw [he] at hh
  convert hh using 1
  dsimp
  rw [← div_eq_mul_inv]
  dsimp [u]
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.div_re, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, pow_two, Complex.I_re, Complex.I_im]
  have htrig := Real.sin_sq_add_cos_sq θ
  have hd : 0 < (1 - q) ^ 2 + 4 * q * Real.cos θ ^ 2 := by
    have hpos : 0 < (1 - q) ^ 2 := sq_pos_of_pos (sub_pos.mpr hq1)
    positivity
  field_simp
  nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]

private def densityTerm (b θ : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  -2 * b ^ 2 * (-b ^ 2) ^ j * Real.cos ((2 * (j : ℝ) + 1) * θ) *
    (t ^ (2 * j + 1) * (1 - t))

private theorem density_integral (b θ : ℝ) (j : ℕ) :
    (∫ t in (0 : ℝ)..1, densityTerm b θ j t) = boundaryTerm b θ j := by
  unfold densityTerm
  rw [intervalIntegral.integral_const_mul]
  have he : (fun t : ℝ => t ^ (2 * j + 1) * (1 - t)) =
      (fun t => t ^ (2 * j + 1) - t ^ (2 * j + 2)) := by
    funext t
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by omega, pow_succ]
    ring
  rw [he, intervalIntegral.integral_sub ((continuous_id.pow _).intervalIntegrable 0 1)
    ((continuous_id.pow _).intervalIntegrable 0 1),
    integral_pow, integral_pow]
  simp only [one_pow, zero_pow (by omega : 2 * j + 1 + 1 ≠ 0),
    zero_pow (by omega : 2 * j + 2 + 1 ≠ 0), sub_zero]
  unfold boundaryTerm
  push_cast
  rw [show -b ^ 2 = (-1 : ℝ) * b ^ 2 by ring, mul_pow, ← pow_mul,
    pow_add]
  simp only [pow_add, pow_one]
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  field_simp
  <;> ring

private theorem kernel_integral_interior (b θ : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    boundaryKernel b θ = -2 * b ^ 2 * Real.cos θ *
      ∫ t in (0 : ℝ)..1, t * (1 - t) * (1 + b ^ 2 * t ^ 2) /
        ((1 - b ^ 2 * t ^ 2) ^ 2 + 4 * b ^ 2 * t ^ 2 * Real.cos θ ^ 2) := by
  have hb2 : b ^ 2 < 1 := by nlinarith
  let U : ℕ → ℝ := fun j => 2 * b ^ 2 * (b ^ 2) ^ j
  have hU : Summable U :=
    (summable_geometric_of_lt_one (sq_nonneg b) hb2).mul_left _
  let R : ℝ → ℝ := fun t => -2 * b ^ 2 * Real.cos θ *
    (t * (1 - t) * (1 + b ^ 2 * t ^ 2) /
      ((1 - b ^ 2 * t ^ 2) ^ 2 + 4 * b ^ 2 * t ^ 2 * Real.cos θ ^ 2))
  have hlim (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      HasSum (fun j => densityTerm b θ j t) (R t) := by
    have hq : b ^ 2 * t ^ 2 < 1 := by
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      nlinarith [sq_nonneg b, sq_nonneg t]
    convert (cosine_geometric (b ^ 2 * t ^ 2) θ (by positivity) hq).mul_left
      (-2 * b ^ 2 * t * (1 - t)) using 1
    · funext j
      dsimp [densityTerm]
      rw [show -(b ^ 2 * t ^ 2) = (-b ^ 2) * t ^ 2 by ring,
        mul_pow, ← pow_mul, pow_succ]
      ring
    · dsimp [R]
      ring
  have hbound (j : ℕ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      ‖densityTerm b θ j t‖ ≤ U j := by
    have ht0 : 0 ≤ t := ht.1.le
    have htP : |t ^ (2 * j + 1)| ≤ 1 := by
      rw [abs_pow, abs_of_nonneg ht0]
      exact pow_le_one₀ ht0 ht.2
    have hsub : |1 - t| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
      linarith [ht.1]
    have hc := Real.abs_cos_le_one ((2 * (j : ℝ) + 1) * θ)
    dsimp [densityTerm, U]
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_ofNat,
      abs_of_nonneg (sq_nonneg b)]
    calc
      _ ≤ 2 * b ^ 2 * (b ^ 2) ^ j * 1 * (1 * 1) := by gcongr
      _ = _ := by ring
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ)) (F := densityTerm b θ) (f := R)
    (fun j (_ : ℝ) => U j)
    (fun j => (show Continuous (densityTerm b θ j) by
      unfold densityTerm; fun_prop).aestronglyMeasurable)
    (fun j => .of_forall (fun t ht => hbound j t (by simpa using ht)))
    (.of_forall (fun _ _ => hU)) intervalIntegrable_const
    (.of_forall (fun t ht => hlim t (by simpa using ht)))
  simp_rw [density_integral] at hsum
  calc
    boundaryKernel b θ = ∫ t in (0 : ℝ)..1, R t := hsum.tsum_eq
    _ = _ := by dsimp [R]; rw [intervalIntegral.integral_const_mul]

private theorem kernel_sign_interior (b θ : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    Real.cos θ * boundaryKernel b θ ≤ 0 := by
  rw [kernel_integral_interior b θ hb0 hb1]
  have hi : 0 ≤ ∫ t in (0 : ℝ)..1,
      t * (1 - t) * (1 + b ^ 2 * t ^ 2) /
        ((1 - b ^ 2 * t ^ 2) ^ 2 + 4 * b ^ 2 * t ^ 2 * Real.cos θ ^ 2) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    exact div_nonneg (by positivity [ht.1, sub_nonneg.mpr ht.2]) (by positivity)
  nlinarith [sq_nonneg (Real.cos θ), sq_nonneg b,
    mul_nonneg (mul_nonneg (sq_nonneg b) (sq_nonneg (Real.cos θ))) hi]

/-- Uniform convergence, continuity, reflection, and the sign of the actual source kernel,
including the entire closed parameter edge `b = 1`. -/
theorem boundary_kernel_control (b θ : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    Continuous (boundaryKernel b) ∧
    boundaryKernel b (Real.pi - θ) = -boundaryKernel b θ ∧
    Real.cos θ * boundaryKernel b θ ≤ 0 := by
  refine ⟨kernel_continuous hb, kernel_reflection b θ, ?_⟩
  have hc : ContinuousOn (fun b => Real.cos θ * boundaryKernel b θ) (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.const_mul
    exact continuousOn_tsum (fun j => by unfold boundaryTerm; fun_prop)
      majorant_summable (fun j b hb => term_norm_le hb θ j)
  have hcl : closure (Ico (0 : ℝ) 1) = Icc (0 : ℝ) 1 := closure_Ico (by norm_num)
  exact le_on_closure (s := Ico (0 : ℝ) 1)
    (f := fun c => Real.cos θ * boundaryKernel c θ) (g := fun _ => 0)
    (fun c hc => kernel_sign_interior c θ hc.1 hc.2)
    (by simpa only [hcl] using hc) continuousOn_const (by simpa only [hcl] using hb)

#print axioms boundary_kernel_control

end D5.S3.Analytic.Interpolation.SchurBoundaryKernel
