/- GID: D5/S3/Quantum/Dynamics/CalibratedUnitaryGroup
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/CalibratedUnitaryGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Differentiation of a unitary group gives its calibrated Hamiltonian and exponential. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousLinearMap.topologicalSpace
attribute [-instance] ContinuousLinearMap.uniformSpace
noncomputable section
namespace D5.S3.Quantum.Dynamics.CalibratedUnitaryGroup

/-- Operator-norm differentiability at zero and the group law determine every time.
The nonzero real calibration is independent of any discrete history count. -/
theorem calibrated_group {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (U : ℝ → H →L[ℂ] H) (G : H →L[ℂ] H)
    (hzero : U 0 = 1) (hgroup : ∀ s t, U (s + t) = U s * U t)
    (hunit : ∀ t, star (U t) * U t = 1)
    (hderiv : HasDerivAt U G 0) (ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    let Hamiltonian := (Complex.I * (ℏ : ℂ)) • G
    IsSelfAdjoint Hamiltonian ∧
    (∀ t, U t = NormedSpace.exp ((-Complex.I * (t : ℂ) / (ℏ : ℂ)) • Hamiltonian)) ∧
    (∀ t, HasDerivAt U ((-Complex.I / (ℏ : ℂ)) • (Hamiltonian * U t)) t) := by
  letI := NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)
  have hd (t : ℝ) : HasDerivAt U (G * U t) t := by
    have hc : HasDerivAt (fun s : ℝ => U (s - t)) G t := by
      simpa [Function.comp_def] using hderiv.scomp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
    have hh := hc.mul_const (U t)
    have hf : (fun s : ℝ => U (s-t) * U t) = U := by
      funext s
      rw [← hgroup, sub_add_cancel]
    rw [hf] at hh
    exact hh
  have hskew : star G = -G := by
    have hh := hderiv.star.mul hderiv
    change HasDerivAt (fun s : ℝ => star (U s) * U s)
      (star G * U 0 + star (U 0) * G) 0 at hh
    have hz : HasDerivAt (fun _ : ℝ => (1 : H →L[ℂ] H)) (star G + G) 0 := by
      simpa only [Pi.mul_apply, hzero, star_one, mul_one, one_mul, hunit] using hh
    have hz' := hz.unique (hasDerivAt_const 0 (1 : H →L[ℂ] H))
    exact eq_neg_of_add_eq_zero_left hz'
  have he (t : ℝ) : U t = NormedSpace.exp (t • G) := by
    let F := fun s : ℝ => NormedSpace.exp (s • (-G)) * U s
    have hF := fun s : ℝ => (hasDerivAt_exp_smul_const (-G) s).mul (hd s)
    simp only [neg_mul, mul_neg, mul_assoc, neg_add_cancel] at hF
    have hc := is_const_of_deriv_eq_zero (fun s => (hF s).differentiableAt)
      (fun s => (hF s).deriv) t 0
    have hFone : NormedSpace.exp (t • (-G)) * U t = 1 := by
      simpa [F, hzero] using hc
    have hinv : NormedSpace.exp (t • G) * NormedSpace.exp (t • (-G)) = 1 := by
      rw [smul_neg]
      rw [← NormedSpace.exp_add_of_commute (Commute.refl (t • G)).neg_right, add_neg_cancel, NormedSpace.exp_zero]
    calc
      U t = (NormedSpace.exp (t • G) * NormedSpace.exp (t • (-G))) * U t := by rw [hinv, one_mul]
      _ = NormedSpace.exp (t • G) := by rw [mul_assoc, hFone, mul_one]
  dsimp only
  have hℏc : (ℏ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℏ
  have hcoef (t : ℝ) : (-Complex.I * (t : ℂ) / (ℏ : ℂ)) *
      (Complex.I * (ℏ : ℂ)) = (t : ℂ) := by
    field_simp [hℏc]
    linear_combination -(t : ℂ) * Complex.I_sq
  refine ⟨?_, ?_, ?_⟩
  · change star ((Complex.I * (ℏ : ℂ)) • G) = _
    rw [star_smul, hskew]
    simp [smul_neg, mul_comm]
  · intro t
    rw [smul_smul, hcoef]
    simpa using he t
  · intro t
    convert hd t using 1
    rw [smul_mul_assoc, smul_smul]
    have hc := hcoef 1
    norm_num at hc
    rw [hc, one_smul]

#print axioms calibrated_group
end D5.S3.Quantum.Dynamics.CalibratedUnitaryGroup
