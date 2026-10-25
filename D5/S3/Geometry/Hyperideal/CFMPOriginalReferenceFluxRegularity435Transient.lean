import D5.S3.Geometry.Hyperideal.CFMPOriginalCellKernel435Transient
import D5.S3.Geometry.Hyperideal.CFMPReferenceSimplexDivergence435Transient

/-! Temporary ambient C1 check for the actual original-cell reference field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Matrix BigOperators ContDiff
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPFrameMotion435Transient
open CFMPFrameContinuity435Transient
open CFMPFrameAffineTransport435Transient
open CFMPOriginalCellsIndependent435Transient
open CFMPActualCellMotion435Transient
open CFMPActualNativeCellMotion435Transient
open CFMPOriginalNativeCoordinates435Transient

namespace CFMPOriginalReferenceFluxRegularity435Transient

theorem original_total_flux_c1
    (l0 : Fin 6 → ℝ) (hl0 : ∀ k, 0 < l0 k)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (K : M4) (n : Fin 20) (E : Matrix (Fin 3) (Fin 3) ℝ)
    (v u : Fin 3 → ℝ)
    (hu : u ∈ CFMPReferenceSimplexDivergence435Transient.simplex) :
    ContDiffAt ℝ 1
      (totalFlux M0 K (edgeMatrix l0 n) E (drop (vertices l0 n 0)) v) u := by
  have hu' : referenceSimplex u := hu
  have hmem := lift_cellPoint_mem_body l0 hl0 n u hu'
  have hq : q M0 (cellPoint l0 n u) ≠ 0 :=
    (original_native_coordinates l0 hl0 M0 f hf
      ⟨lift (cellPoint l0 n u),hmem⟩).1.ne'
  have hx : ContDiff ℝ 1 (cellPoint l0 n) := by
    exact contDiff_const.add (edgeMatrix l0 n).mulVecLin.toContinuousLinearMap.contDiff
  have hrho : ContDiffAt ℝ 1 (fun z => density M0 (cellPoint l0 n z)) u := by
    open scoped Matrix.Norms.Elementwise in
      exact CFMPOriginalCellKernel435Transient.density_c1
        (fun _ : Fin 3 → ℝ => M0) (cellPoint l0 n) u
        contDiffAt_const hx.contDiffAt hm0 hq
  have hfield : ContDiff ℝ 1 (field K) := by
    apply contDiff_pi.mpr
    intro i
    simp [field,alpha,lift,rowSum,Fin.sum_univ_four]
    fun_prop
  have hw : ContDiff ℝ 1
      (fun z : Fin 3 → ℝ => v+E.mulVec z+field K (cellPoint l0 n z)) :=
    (contDiff_const.add E.mulVecLin.toContinuousLinearMap.contDiff).add (hfield.comp hx)
  have hscalar : ContDiffAt ℝ 1
      (fun z => |(edgeMatrix l0 n).det| * density M0 (cellPoint l0 n z)) u :=
    contDiffAt_const.mul hrho
  have hlinear : ContDiffAt ℝ 1
      (fun z => (edgeMatrix l0 n)⁻¹.mulVec
        (v+E.mulVec z+field K (cellPoint l0 n z))) u :=
    ((edgeMatrix l0 n)⁻¹).mulVecLin.toContinuousLinearMap.contDiff.contDiffAt.comp u
      hw.contDiffAt
  change ContDiffAt ℝ 1
    (fun z : Fin 3 → ℝ =>
      (|(edgeMatrix l0 n).det| * density M0 (cellPoint l0 n z)) •
        (edgeMatrix l0 n)⁻¹.mulVec
          (v+E.mulVec z+field K (cellPoint l0 n z))) u
  exact hscalar.smul hlinear

end CFMPOriginalReferenceFluxRegularity435Transient
