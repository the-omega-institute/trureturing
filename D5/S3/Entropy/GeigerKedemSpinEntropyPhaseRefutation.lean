/- GID: D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation
   generality: I
   mirror-B: D5/B/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.claim; result=D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.result; claim=D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.claim
   digest: The spin-1 entropy changes by 1/891 between two relative phases. -/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

open Complex MeasureTheory Set Metric
open scoped Topology

namespace D5.S3.Entropy.GeigerKedemSpinEntropyPhaseRefutation

noncomputable def shannonTerm (p : ℝ) : ℝ :=
  -(p * Real.log p) -
    (1 - p) * Real.log (1 - p)

noncomputable def density
    (thetaAlpha thetaBeta phaseX phaseZ phi : ℝ) : ℝ :=
  Complex.normSq
    (((Real.sin thetaAlpha * Real.cos thetaBeta : ℝ) : ℂ) *
        Complex.exp
          (((phaseX + 2 * phi : ℝ) : ℂ) * Complex.I) +
      (Real.cos thetaAlpha : ℂ) *
        Complex.exp ((phi : ℂ) * Complex.I) +
      ((Real.sin thetaAlpha * Real.sin thetaBeta : ℝ) : ℂ) *
        Complex.exp
          (((phaseZ - 2 * phi : ℝ) : ℂ) * Complex.I)) /
    (2 * Real.pi)

noncomputable def spinEntropy
    (thetaAlpha thetaBeta phaseX phaseZ : ℝ) : ℝ :=
  -(∫ phi in (0 : ℝ)..(2 * Real.pi),
      density thetaAlpha thetaBeta phaseX phaseZ phi *
        Real.log
          (density thetaAlpha thetaBeta phaseX phaseZ phi)) +
    shannonTerm (Real.cos thetaAlpha ^ 2) +
    Real.sin thetaAlpha ^ 2 *
      shannonTerm (Real.cos thetaBeta ^ 2)

def claim : Prop :=
  ∀ thetaAlpha thetaBeta phaseX phaseZ : ℝ,
    thetaAlpha ∈ Set.Icc 0 (Real.pi / 2) →
    thetaBeta ∈ Set.Icc 0 (Real.pi / 2) →
    phaseX ∈ Set.Ico 0 (2 * Real.pi) →
    phaseZ ∈ Set.Ico 0 (2 * Real.pi) →
    spinEntropy thetaAlpha thetaBeta phaseX phaseZ =
      spinEntropy thetaAlpha thetaBeta 0 0

private theorem density_continuous (a b x z : ℝ) : Continuous (density a b x z) := by
  unfold density
  fun_prop

private theorem density_mul_log_intervalIntegrable (a b x z : ℝ) :
    IntervalIntegrable (fun t => density a b x z t * Real.log (density a b x z t))
      volume 0 (2 * Real.pi) :=
  (Real.continuous_mul_log.comp (density_continuous a b x z)).intervalIntegrable _ _

private def poly (s : ℝ) (z : ℂ) : ℂ := 3 + z + (s : ℂ) * z ^ 4

private noncomputable def logPoly (s : ℝ) (z : ℂ) : ℂ :=
  poly s z * Complex.log (poly s z)

private theorem poly_differentiable (s : ℝ) : Differentiable ℂ (poly s) := by
  unfold poly
  fun_prop

private theorem poly_re_lower (s : ℝ) (hs : |s| ≤ 1) (z : ℂ)
    (hz : z ∈ closedBall 0 1) : 1 ≤ (poly s z).re := by
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  have hpow : ‖z ^ 4‖ ≤ 1 := by simpa [norm_pow] using pow_le_one₀ (n := 4) (norm_nonneg z) hz'
  have hmul : ‖(s : ℂ) * z ^ 4‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul hs hpow (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have h1 := (abs_le.mp (Complex.abs_re_le_norm z)).1
  have h2 := (abs_le.mp (Complex.abs_re_le_norm ((s : ℂ) * z ^ 4))).1
  simp only [poly, add_re]
  norm_num at *
  linarith

private theorem poly_slit (s : ℝ) (hs : |s| ≤ 1) (z : ℂ)
    (hz : z ∈ closedBall 0 1) : poly s z ∈ Complex.slitPlane := by
  exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [poly_re_lower s hs z hz]))

private theorem logPoly_differentiableOn (s : ℝ) (hs : |s| ≤ 1) :
    DifferentiableOn ℂ (logPoly s) (closedBall 0 1) := by
  exact (poly_differentiable s).differentiableOn.mul
    ((poly_differentiable s).differentiableOn.clog (poly_slit s hs))

private theorem circleAverage_div_pow (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) (n : ℕ) :
    Real.circleAverage (fun z => f z / z ^ n) 0 1 =
      iteratedDeriv n f 0 / (n.factorial : ℂ) := by
  rw [Real.circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0)]
  have heq : (fun z : ℂ => (z - 0)⁻¹ • (f z / z ^ n)) =
      (fun z => (1 / (z - 0) ^ (n + 1)) • f z) := by
    funext z
    simp only [sub_zero, smul_eq_mul, pow_succ, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [heq, DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul
    (by norm_num : (0 : ℝ) < 1) n hf]
  simp only [smul_eq_mul]
  field_simp

end D5.S3.Entropy.GeigerKedemSpinEntropyPhaseRefutation
