/- GID: D5/S3/Analytic/ConvexBarrier/HomogeneousHessian
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/HomogeneousHessian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Analytic.ConvexBarrier.PrimalDikin
import D5.S3.Analytic.ConvexBarrier.ScalarAlgebra
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Euler and Hessian identities actually differentiated from the homogeneity
field of `Basic.IsLHSCB`. These supply the primal coordinates of
Zhang--Fu--Dai, arXiv:2611.06404v1, (2.3), (3.6), and the primal
quadratic used in (3.8).

In particular the primal quadratic normalization is a proved identity,
not a user-supplied identity or an unexplained exclusion premise.
The inverse Hessian/conjugate construction is not asserted in this file.
SOURCE ONLY. No Lean elaboration or kernel execution has been performed.
-/

open Set Filter
open scoped Topology ContDiff

namespace D5.S3.Analytic.ConvexBarrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def hessian (F : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ F) x

noncomputable def normalizedFirst (ν : ℝ) (F : E → ℝ) (x h : E) : ℝ :=
  fderiv ℝ F x h / ν

noncomputable def projectiveHessian (ν : ℝ) (D : Set E)
    (F : E → ℝ) (x h : E) : ℝ :=
  diagonal 2 D F x h / ν - normalizedFirst ν F x h ^ 2

theorem IsLHSCB.parameter_pos {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) : 0 < ν := lt_of_lt_of_le zero_lt_one hF.parameter

/-- Euler's identity with the barrier sign: DF(x)[x] = -nu. -/
theorem IsLHSCB.euler {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) :
    fderiv ℝ F x x = -ν := by
  have hdiff := (hF.smooth.contDiffAt
    (hF.domain_open.mem_nhds hx)).differentiableAt (by norm_num)
  have hleft : HasDerivAt (fun t : ℝ => F (t • x)) (fderiv ℝ F x x) 1 := by
    simpa [Function.comp_def, id_eq] using hdiff.hasFDerivAt.comp_hasDerivAt_of_eq
      1 ((hasDerivAt_id (1 : ℝ)).smul_const x) (by simp)
  have hright : HasDerivAt (fun t : ℝ => F x-ν*Real.log t) (-ν) 1 := by
    convert (hasDerivAt_const (1 : ℝ) (F x)).sub
      (((hasDerivAt_id (1 : ℝ)).log one_ne_zero).const_mul ν) using 1
    · funext t
      simp [id_eq]
    · norm_num
  have heq : (fun t : ℝ => F (t • x)) =ᶠ[𝓝 (1 : ℝ)]
      (fun t => F x-ν*Real.log t) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num)] with t ht
    exact hF.homogeneous x hx t ht
  exact hleft.unique (hright.congr_of_eventuallyEq heq)

/-- Differentiate Euler on the actual open domain. No symmetry or mixed
derivative identity is postulated. This fixes the first Hessian slot. -/
theorem IsLHSCB.hessian_euler {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (h : E) :
    hessian F x h x = -fderiv ℝ F x h := by
  have hC := hF.smooth.contDiffAt (hF.domain_open.mem_nhds hx)
  have hgrad : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he := hgrad.hasFDerivAt.clm_apply (hasFDerivAt_id x)
  have heq : (fun y : E => fderiv ℝ F y y) =ᶠ[𝓝 x] (fun _ => -ν) := by
    filter_upwards [hF.domain_open.mem_nhds hx] with y hy
    exact hF.euler hy
  have hezero : HasFDerivAt (fun _ : E => -ν) (0 : E →L[ℝ] ℝ) x :=
    hasFDerivAt_const (-ν) x
  have hezero := hezero.congr_of_eventuallyEq heq
  have hzero := congrArg (fun L : E →L[ℝ] ℝ => L h) (he.unique hezero)
  change fderiv ℝ F x h + hessian F x h x = 0 at hzero
  linarith

/-- Both mixed radial Hessian entries, derived using actual C2 symmetry. -/
theorem IsLHSCB.hessian_radial_coordinates {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (h : E) :
    hessian F x x x = ν ∧
    hessian F x x h = -fderiv ℝ F x h ∧
    hessian F x h x = -fderiv ℝ F x h := by
  have hC := hF.smooth.contDiffAt (hF.domain_open.mem_nhds hx)
  have hs := hC.isSymmSndFDerivAt (by norm_num)
  refine ⟨?_, ?_, hF.hessian_euler hx h⟩
  · rw [hF.hessian_euler hx x, hF.euler hx, neg_neg]
  · change fderiv ℝ (fderiv ℝ F) x x h = -fderiv ℝ F x h
    rw [hs.eq x h]
    exact hF.hessian_euler hx h

theorem IsLHSCB.diagonal_two_eq_hessian {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (h : E) :
    diagonal 2 D F x h = hessian F x h h := by
  unfold diagonal
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hF.domain_open.uniqueDiffOn
    ((hF.smooth.contDiffAt (hF.domain_open.mem_nhds hx)).of_le (by norm_num)) hx]
  exact iteratedFDeriv_two_apply F x (fun _ => h)

/-- Actual primal metric polynomial at an arbitrary affine endpoint.
Neither delta nor t is restricted, so the negative chord direction is
obtained by replacing delta by -deltaMinus. -/
theorem IsLHSCB.primal_chord_polynomial {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (h : E) (δ t : ℝ) :
    diagonal 2 D F x (t • (x+δ • h)-x) =
      primalQuadratic ν (1-normalizedFirst ν F x h*δ)
        (projectiveHessian ν D F x h*δ^2) t := by
  have hn : ν ≠ 0 := hF.parameter_pos.ne'
  obtain ⟨hxx, hxh, hhx⟩ := hF.hessian_radial_coordinates hx h
  have hw : t • (x+δ • h)-x = (t-1) • x+(t*δ) • h := by
    rw [smul_add, smul_smul, sub_smul, one_smul]
    abel
  rw [hF.diagonal_two_eq_hessian hx, hw]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hxx, hxh, hhx, ← hF.diagonal_two_eq_hessian hx h]
  unfold primalQuadratic projectiveHessian normalizedFirst
  field_simp [hn]
  <;> ring

/-- The normalized projective Hessian is strictly positive on every
nonradial direction; it is the actual Hessian Schur complement. -/
theorem IsLHSCB.projectiveHessian_pos {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (h : E)
    (hnonradial : ∀ t : ℝ, h ≠ t • x) :
    0 < projectiveHessian ν D F x h := by
  let a := normalizedFirst ν F x h
  let v := h+a • x
  have hv : v ≠ 0 := by
    intro hz
    apply hnonradial (-a)
    have hh : h = -(a • x) := by
      calc
        h = (h+a • x)-a • x := by abel
        _ = -(a • x) := by rw [show h+a • x = 0 from hz, zero_sub]
    simpa only [neg_smul] using hh
  have hpos := hF.hessian_pos x hx v hv
  have hn : ν ≠ 0 := hF.parameter_pos.ne'
  obtain ⟨hxx, hxh, hhx⟩ := hF.hessian_radial_coordinates hx h
  have heq : diagonal 2 D F x v = ν*projectiveHessian ν D F x h := by
    rw [hF.diagonal_two_eq_hessian hx]
    dsimp [v]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hxx, hxh, hhx, ← hF.diagonal_two_eq_hessian hx h]
    dsimp [a, projectiveHessian, normalizedFirst]
    field_simp [hn]
    <;> ring
  rw [heq] at hpos
  exact (mul_pos_iff_of_pos_left hF.parameter_pos).mp hpos

end D5.S3.Analytic.ConvexBarrier
