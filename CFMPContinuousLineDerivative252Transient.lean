import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
set_option autoImplicit false
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace CFMPContinuousLineDerivative252Transient

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Operator-norm continuity of the line-derivative field gives a Frechet derivative,
without assuming continuity of the function itself. -/
theorem hasFDerivAt_of_continuous_line_field
    {U : Set E} (hU : IsOpen U) {f : E → F} {A : E → E →L[ℝ] F}
    (hline : ∀ (a v : E) (t : ℝ), a + t • v ∈ U →
      HasDerivAt (fun s : ℝ => f (a + s • v)) (A (a + t • v) v) t)
    {x : E} (hx : x ∈ U) (hA : ContinuousAt A x) :
    HasFDerivAt f (A x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,isLittleO_iff]
  intro ε hε
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ ‖A y - A x‖ < ε := by
    have hsmall := (Metric.tendsto_nhds.mp hA) ε hε
    filter_upwards [hU.mem_nhds hx,hsmall] with y hy hAy
    exact ⟨hy,by simpa only [dist_eq_norm] using hAy⟩
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp hnear
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
  have hh' : ‖h‖ < δ := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  have hsegment (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      x + t • h ∈ U ∧ ‖A (x + t • h) - A x‖ < ε := by
    apply hnear
    calc
      dist (x + t • h) x = t * ‖h‖ := by
        simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg ht.1]
      _ ≤ ‖h‖ := mul_le_of_le_one_left (norm_nonneg h) ht.2
      _ < δ := hh'
  let ψ : ℝ → F := fun t => f (x + t • h) - t • (A x h)
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt ψ ((A (x + t • h) - A x) h) (Icc (0 : ℝ) 1) t := by
    have hd := (hline x h t (hsegment t ht).1).sub
      ((hasDerivAt_id t).smul_const (A x h))
    convert! hd.hasDerivWithinAt using 1 <;>
      simp only [ψ,one_smul,ContinuousLinearMap.sub_apply,Pi.sub_apply,id_eq]
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖(A (x + t • h) - A x) h‖ ≤ ε * ‖h‖ := by
    exact ((A (x + t • h) - A x).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right (hsegment t ht).2.le (norm_nonneg h))
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := ψ) (f' := fun t => (A (x + t • h) - A x) h)
    (x := (0 : ℝ)) (y := (1 : ℝ))
    hderiv hbound (convex_Icc (0 : ℝ) 1)
    (by constructor <;> norm_num) (by constructor <;> norm_num)
  have heq : ψ 1 - ψ 0 = f (x + h) - f x - A x h := by
    dsimp only [ψ]
    simp only [one_smul,zero_smul,add_zero,sub_zero]
    abel
  simpa only [heq,sub_zero,norm_one,mul_one] using hmv

/-- A continuous operator-valued line-derivative field on an open set is the
continuous Frechet derivative of the same function on that set. -/
theorem contDiffOn_one_of_continuous_line_field
    {U : Set E} (hU : IsOpen U) {f : E → F} {A : E → E →L[ℝ] F}
    (hline : ∀ (a v : E) (t : ℝ), a + t • v ∈ U →
      HasDerivAt (fun s : ℝ => f (a + s • v)) (A (a + t • v) v) t)
    (hA : ContinuousOn A U) :
    ContDiffOn ℝ 1 f U ∧ ∀ x ∈ U, HasFDerivAt f (A x) x := by
  have hd (x : E) (hx : x ∈ U) : HasFDerivAt f (A x) x :=
    hasFDerivAt_of_continuous_line_field hU hline hx
      ((hA x hx).continuousAt (hU.mem_nhds hx))
  refine ⟨?_,hd⟩
  have hc : ContDiffOn ℝ (0 + 1) f U :=
    (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (n := 0) hU.uniqueDiffOn).2
      ⟨by simp,A,contDiffOn_zero.mpr hA,
        fun x hx => (hd x hx).hasFDerivWithinAt⟩
  simpa only [zero_add] using hc

end CFMPContinuousLineDerivative252Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPContinuousLineDerivative252Transient.hasFDerivAt_of_continuous_line_field,
      ``CFMPContinuousLineDerivative252Transient.contDiffOn_one_of_continuous_line_field] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP252 theorem absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP252 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP252 CHECKED {name} axioms={axioms}"
