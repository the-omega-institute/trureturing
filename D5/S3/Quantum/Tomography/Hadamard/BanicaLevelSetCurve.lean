/- GID: D5/S3/Quantum/Tomography/Hadamard/BanicaLevelSetCurve
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/Hadamard/BanicaLevelSetCurve
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: An analytic regular level set contains global analytic curves with prescribed tangent direction up to positive scaling. -/

import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open scoped Topology ContDiff
open Filter

noncomputable section

namespace D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve

private def squash (r t : ℝ) : ℝ := r * t / Real.sqrt (1 + t ^ 2)

private theorem squash_contDiff (r : ℝ) : ContDiff ℝ ⊤ (squash r) := by
  unfold squash
  exact (contDiff_const.mul contDiff_id).div
    ((contDiff_const.add (contDiff_id.pow 2)).sqrt (fun t => by positivity))
    (fun t => ne_of_gt (Real.sqrt_pos.2 (by positivity)))

private theorem squash_bound {r : ℝ} (hr : 0 < r) (t : ℝ) : |squash r t| < r := by
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + t ^ 2 by positivity)
  have ht : |t| < Real.sqrt (1 + t ^ 2) := by
    nlinarith [sq_abs t, abs_nonneg t]
  unfold squash
  rw [abs_div, abs_mul, abs_of_pos hr, abs_of_pos hs]
  exact (div_lt_iff₀ hs).2 (by nlinarith)

private theorem squash_hasDerivAt (r : ℝ) : HasDerivAt (squash r) r 0 := by
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2)) 0 0 := by
    convert (Real.hasDerivAt_sqrt (show (1 + (0 : ℝ) ^ 2) ≠ 0 by norm_num)).comp 0
      ((hasDerivAt_const 0 (1 : ℝ)).add ((hasDerivAt_id (0 : ℝ)).pow 2)) using 1 <;> norm_num [Function.comp_def, Pi.add_apply, Pi.pow_apply]
  convert ((hasDerivAt_id (0 : ℝ)).const_mul r).div hs (by norm_num) using 1 <;>
    simp [squash]
  funext t
  rfl

/-- An analytic curve germ extends by a bounded analytic reparametrization.
Its tangent is multiplied by a strictly positive real number. -/
theorem globalize_analytic_curve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℝ → E) (v : E) (hq : ContDiffAt ℝ ⊤ q 0)
    (hd : HasDerivAt q v 0) (hzero : q 0 = 0)
    (P : E → Prop) (hP : ∀ᶠ t in 𝓝 (0 : ℝ), P (q t)) :
    ∃ (c : ℝ → E) (κ : ℝ), 0 < κ ∧ ContDiff ℝ ⊤ c ∧ c 0 = 0 ∧
      HasDerivAt c (κ • v) 0 ∧ ∀ t, P (c t) := by
  obtain ⟨u, hu, hqu⟩ := hq.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hu hP)
  let c : ℝ → E := fun t => q (squash r t)
  have hmem (t : ℝ) : squash r t ∈ u ∧ P (q (squash r t)) := by
    apply hru
    simpa [Real.dist_eq] using squash_bound hr t
  refine ⟨c, r, hr, ?_, ?_, ?_, fun t => (hmem t).2⟩
  · exact hqu.comp_contDiff (squash_contDiff r) (fun t => (hmem t).1)
  · simpa [c, squash] using hzero
  · simpa [c, Function.comp_def] using
      hd.scomp_of_eq 0 (squash_hasDerivAt r) (by simp [squash])

/-- Every tangent direction of a regular analytic level set is realized by a global
analytic curve in that level set, with a positive rescaling of the tangent. -/
theorem analytic_level_set_curve
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (Φ : E → F) (hΦ : ContDiff ℝ ⊤ Φ) (hzero : Φ 0 = 0)
    (hsurj : Function.Surjective (fderiv ℝ Φ 0))
    (v : E) (hv : fderiv ℝ Φ 0 v = 0) :
    ∃ (c : ℝ → E) (κ : ℝ), 0 < κ ∧ ContDiff ℝ ⊤ c ∧ c 0 = 0 ∧
      HasDerivAt c (κ • v) 0 ∧ ∀ t, Φ (c t) = 0 := by
  letI := FiniteDimensional.complete ℝ E
  letI := FiniteDimensional.complete ℝ F
  let L := fderiv ℝ Φ 0
  have hL : L.range = ⊤ := LinearMap.range_eq_top.2 hsurj
  have hf : HasStrictFDerivAt Φ L 0 := hΦ.contDiffAt.hasStrictFDerivAt (by simp)
  let hc := L.ker_closedComplemented_of_finiteDimensional_range
  let d := hf.implicitFunctionDataOfComplemented Φ L hL hc
  let ψ : L.ker → E := d.implicitFunction (Φ 0)
  have hψ0 : ψ 0 = 0 := by
    exact hf.implicitFunctionOfComplemented_apply_image hL hc
  have hψd : HasStrictFDerivAt ψ L.ker.subtypeL 0 :=
    hf.to_implicitFunctionOfComplemented hL hc
  have hψsmooth : ContDiffAt ℝ ⊤ ψ 0 := by
    have hl : ContDiffAt ℝ ⊤ d.leftFun d.pt := hΦ.contDiffAt
    have hr : ContDiffAt ℝ ⊤ d.rightFun d.pt := by
      dsimp [d, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
      fun_prop
    have hh := d.contDiffAt_implicitFunction hl hr (by simp : (⊤ : ℕ∞ω) ≠ 0)
    have hp0 : d.prodFun d.pt = (Φ 0, (0 : L.ker)) := by
      simp [d, HasStrictFDerivAt.implicitFunctionDataOfComplemented,
        ImplicitFunctionData.prodFun]
    rw [hp0] at hh
    exact hh.comp (0 : L.ker)
      (contDiffAt_const.prodMk (contDiffAt_id (𝕜 := ℝ)))
  let w : L.ker := ⟨v, hv⟩
  let q : ℝ → E := fun t => ψ (t • w)
  have hqs : ContDiffAt ℝ ⊤ q 0 := by
    have hline : ContDiffAt ℝ ⊤ (fun t : ℝ => t • w) 0 := by fun_prop
    have hψsmooth' : ContDiffAt ℝ ⊤ ψ ((0 : ℝ) • w) := by
      simpa using hψsmooth
    exact hψsmooth'.comp 0 hline
  have hqd : HasDerivAt q v 0 := by
    have hline : HasDerivAt (fun t : ℝ => t • w) w 0 :=
      by simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
    simpa [q, w, Function.comp_def] using hψd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hq0 : q 0 = 0 := by simpa [q] using hψ0
  have hqlevel : ∀ᶠ t in 𝓝 (0 : ℝ), Φ (q t) = 0 := by
    have hp := hf.map_implicitFunctionOfComplemented_eq hL hc
    have hcont : ContinuousAt (fun t : ℝ => (Φ 0, t • w)) 0 := by fun_prop
    have ht : Tendsto (fun t : ℝ => (Φ 0, t • w)) (𝓝 0) (𝓝 (Φ 0, 0)) := by
      simpa using hcont.tendsto
    have hh := ht.eventually hp
    simpa [q, ψ, d, hzero, HasStrictFDerivAt.implicitFunctionOfComplemented] using hh
  exact globalize_analytic_curve q v hqs hqd hq0 (fun x => Φ x = 0) hqlevel

end D5.S3.Quantum.Tomography.Hadamard.BanicaLevelSetCurve
