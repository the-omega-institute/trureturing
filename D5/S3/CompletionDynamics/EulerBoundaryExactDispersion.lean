/- GID: D5/S3/CompletionDynamics/EulerBoundaryExactDispersion
   generality: I
   mirror-B: D5/B/S3/CompletionDynamics/EulerBoundaryExactDispersion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact Euler-boundary log-cosh dispersion yields tanh rapidity laws. -/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/- Library-search audit trail (2026-09-02):
   * Six-way repository searches covered energy/velocity terminology, `cosh` and
     `tanh` spellings, digestion receipts and digests, generalized derivative
     and hyperbolic-transport owners, and every in-flight math lane. No current
     or in-flight declaration covers this atom.
   * Pinned Mathlib provides the exact analytic ingredients `deriv_comp`,
     `deriv_comp_mul_left`, `Real.deriv_cosh`, `Real.deriv_log`,
     `Real.exp_log`, `Real.tanh_eq_sinh_div_cosh`, and `Real.cosh_pos`;
     they are applied below.
   * The positivity proof for `cInfinity` uses `Real.pi_pos`, so the normalized
     velocity cannot exploit Lean's totalized division at zero. Likewise,
     `Real.cosh_pos` excludes the totalized nonpositive branch of `Real.log`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.EulerBoundaryExactDispersion

/-- The limiting speed scale in the source normalization. -/
def cInfinity : ℝ := Real.pi / 2

/-- The rapidity coordinate associated with the Euler-boundary wave number. -/
def rapidity (k : ℝ) : ℝ := cInfinity * k

/-- The exact Euler-boundary dispersion relation. -/
def eulerBoundaryEnergy (k : ℝ) : ℝ :=
  Real.log (Real.cosh (rapidity k))

/-- Group velocity is the ordinary real derivative of the dispersion. -/
def eulerBoundaryVelocity (k : ℝ) : ℝ :=
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : NormedSpace ℝ ℝ := NormedAlgebra.toNormedSpace ℝ
  deriv eulerBoundaryEnergy k

/-- The log-cosh dispersion has the exact tanh derivative, and exponentiation
and speed normalization give the source's two rapidity identities. -/
theorem euler_boundary_exact_dispersion (k : ℝ) :
    eulerBoundaryEnergy k =
        Real.log (Real.cosh (Real.pi * k / 2)) ∧
      eulerBoundaryVelocity k =
        cInfinity * Real.tanh (rapidity k) ∧
      Real.exp (eulerBoundaryEnergy k) = Real.cosh (rapidity k) ∧
      eulerBoundaryVelocity k / cInfinity = Real.tanh (rapidity k) := by
  have hSpeedPos : 0 < cInfinity := by
    exact div_pos Real.pi_pos (by norm_num)
  have hVelocity :
      eulerBoundaryVelocity k = cInfinity * Real.tanh (rapidity k) := by
    unfold eulerBoundaryVelocity eulerBoundaryEnergy rapidity
    calc
      deriv (fun x : ℝ => Real.log (Real.cosh (cInfinity * x))) k =
          cInfinity • deriv (fun x : ℝ => Real.log (Real.cosh x))
            (cInfinity * k) :=
        deriv_comp_mul_left cInfinity
          (fun x : ℝ => Real.log (Real.cosh x)) k
      _ = cInfinity * Real.tanh (cInfinity * k) := by
        simp only [smul_eq_mul]
        congr 1
        change deriv (Real.log ∘ Real.cosh) (cInfinity * k) =
          Real.tanh (cInfinity * k)
        rw [deriv_comp (h₂ := Real.log) (h := Real.cosh)
          (x := cInfinity * k)
          (Real.differentiableAt_log (Real.cosh_pos (cInfinity * k)).ne')
          Real.differentiableAt_cosh,
          Real.deriv_log, Real.deriv_cosh,
          Real.tanh_eq_sinh_div_cosh, div_eq_mul_inv]
        ring
  refine ⟨?_, hVelocity, ?_, ?_⟩
  · unfold eulerBoundaryEnergy
    congr 2
    unfold rapidity cInfinity
    ring
  · simpa only [eulerBoundaryEnergy] using
      Real.exp_log (Real.cosh_pos (rapidity k))
  · rw [hVelocity]
    exact mul_div_cancel_left₀ (Real.tanh (rapidity k)) hSpeedPos.ne'

#print axioms euler_boundary_exact_dispersion

end D5.S3.CompletionDynamics.EulerBoundaryExactDispersion
