/- GID: D5/S3/Quantum/Tomography/SublevelRowEnclosure
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/SublevelRowEnclosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A scalar directional mean-value bound encloses every small-residual point in an inflated preconditioned Newton row. -/

import D5.S3.Quantum.Tomography.CayleyCoverAnalysis
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/- Reuse audit (2026-09-06):
   * Reuses the lane's CayleyCoverAnalysis and Mathlib's actual derivative API.
   * The scalar Convex.norm_image_sub_le_of_norm_hasDerivWithin_le theorem
     supplies the analytic estimate, without a shared vector mean-value point.
   * No second interval, root, Cayley, Hadamard, or context carrier is created.
   * The directional bound is the one obtained by summing outward interval
     bounds for each (I-CJ) entry times the corresponding box displacement.
   * This closes one analytic step only. Interval-expression enclosure and
     the whole finite split/contract tree still need their own kernel proofs.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.SublevelRowEnclosure

/-- For any small-residual point `x`, the selected output coordinate lies in
an inflated Newton row centered at `observe m - precondition (f m)`.

`radius` bounds the directional derivative along the actual segment from
`m` to `x`. The extra `norm(precondition) * eta` is indispensable when
`f x` is merely small rather than zero. An interval implementation may use
one such theorem per row; no common mean-value point is required. -/
theorem preconditioned_sublevel_row_enclosure
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (J : E → E →L[ℝ] F)
    (observe : E →L[ℝ] ℝ) (precondition : F →L[ℝ] ℝ)
    (m x : E) (radius eta : ℝ)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasFDerivAt f (J (m + t • (x - m))) (m + t • (x - m)))
    (hdirectional : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖observe (x - m) - precondition (J (m + t • (x - m)) (x - m))‖ ≤ radius)
    (hresidual : ‖f x‖ ≤ eta) :
    ‖observe x - (observe m - precondition (f m))‖ ≤
      radius + ‖precondition‖ * eta := by
  let path : ℝ → E := fun t ↦ m + t • (x - m)
  let g : ℝ → ℝ := fun t ↦ observe (path t) - precondition (f (path t))
  have hpath (t : ℝ) : HasDerivAt path (x - m) t := by
    simpa only [path, one_smul] using
      ((hasDerivAt_id t).smul_const (x - m)).const_add m
  have hg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt g
        (observe (x - m) - precondition (J (path t) (x - m))) t := by
    have houter : HasFDerivAt
        (fun z ↦ observe z - precondition (f z))
        (observe - precondition.comp (J (path t))) (path t) :=
      observe.hasFDerivAt.sub
        (precondition.hasFDerivAt.comp (path t) (hderiv t ht))
    simpa only [g, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
      using houter.comp_hasDerivAt t (hpath t)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht ↦ (hg t ht).hasDerivWithinAt)
    hdirectional (convex_Icc (0 : ℝ) 1)
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
  have hzero : path 0 = m := by simp only [path, zero_smul, add_zero]
  have hone : path 1 = x := by
    simp only [path, one_smul]
    abel
  have hgzero : g 0 = observe m - precondition (f m) := by rw [g, hzero]
  have hgone : g 1 = observe x - precondition (f x) := by rw [g, hone]
  have hdiff :
      ‖(observe x - precondition (f x)) - (observe m - precondition (f m))‖ ≤
        radius := by
    simpa only [hgzero, hgone, sub_zero, norm_one, mul_one] using hmv
  have hsmall : ‖precondition (f x)‖ ≤ ‖precondition‖ * eta :=
    le_trans (precondition.le_opNorm (f x))
      (mul_le_mul_of_nonneg_left hresidual (norm_nonneg precondition))
  calc
    ‖observe x - (observe m - precondition (f m))‖ =
        ‖((observe x - precondition (f x)) -
          (observe m - precondition (f m))) + precondition (f x)‖ := by
      congr 1
      ring
    _ ≤ ‖(observe x - precondition (f x)) - (observe m - precondition (f m))‖ +
        ‖precondition (f x)‖ := norm_add_le _ _
    _ ≤ radius + ‖precondition‖ * eta := add_le_add hdiff hsmall

#print axioms preconditioned_sublevel_row_enclosure

end D5.S3.Quantum.Tomography.SublevelRowEnclosure
