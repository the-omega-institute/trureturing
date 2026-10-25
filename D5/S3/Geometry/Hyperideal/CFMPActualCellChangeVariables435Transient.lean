import D5.S3.Geometry.Hyperideal.CFMPOriginalCellIntegral435Transient
import D5.S3.Geometry.Hyperideal.CFMPNativeTwentyCellVolume435Transient
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Set MeasureTheory
open CFMPActualCellMotion435Transient CFMPActualNativeCellMotion435Transient
open CFMPOriginalCellsIndependent435Transient
open CFMPCompactKernelTube435Transient (delta delta_compact)
open CFMPOriginalFrameDensity435Transient (originalDensity)
open CFMPTwentyCellIntegralAssembly435Transient (C K)
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace

namespace CFMPActualCellChangeVariables435Transient

theorem cellPoint_image (l : Fin 6 → ℝ) (n : Fin 20) :
    cellPoint l n '' delta = C l n := by
  apply Subset.antisymm
  · rintro z ⟨u,hu,rfl⟩
    refine ⟨coefficientPoint l n u,?_,drop_coefficientPoint l n u⟩
    exact mem_convexHull_of_exists_fintype _ _
      (weights_nonnegative u hu) (weights_sum u) (fun j => ⟨j,rfl⟩) rfl
  · rintro z ⟨x,hx,rfl⟩
    obtain ⟨a,ha,hsum,he⟩ := CFMPCellIntersections435Transient.hull_weights
      (vertices l n) x hx
    let u : Fin 3 → ℝ := fun j => a j.succ
    have hsum' : a 0 + ∑ j : Fin 3, u j = 1 := by
      simpa only [Fin.sum_univ_succ,u] using hsum
    have hu : u ∈ delta := ⟨fun j => ha j.succ,by linarith [ha 0]⟩
    have hw : weights u = a := by
      funext j
      cases j using Fin.cases with
      | zero => simp only [weights,Fin.cons_zero]; linarith
      | succ j => rfl
    have hp : coefficientPoint l n u = x := by
      simpa only [coefficientPoint,hw,CFMPCellIntersections435Transient.mix] using he
    refine ⟨u,hu,?_⟩
    rw [← drop_coefficientPoint,hp]
    rfl

theorem cellPoint_hasFDerivAt (l : Fin 6 → ℝ) (n : Fin 20) (u : Fin 3 → ℝ) :
    HasFDerivAt (cellPoint l n)
      (edgeMatrix l n).mulVecLin.toContinuousLinearMap u := by
  unfold cellPoint
  change HasFDerivAt
    (fun v => drop (vertices l n 0) + (edgeMatrix l n).mulVecLin.toContinuousLinearMap v)
    (edgeMatrix l n).mulVecLin.toContinuousLinearMap u
  exact (edgeMatrix l n).mulVecLin.toContinuousLinearMap.hasFDerivAt.const_add
    (drop (vertices l n 0))

theorem cellPoint_injective (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i) (n : Fin 20) :
    Function.Injective (cellPoint l n) := by
  intro u v h
  apply Matrix.mulVec_injective_of_det_ne_zero (edgeMatrix_det_ne_zero l hl n)
  exact add_left_cancel h

theorem actual_cell_integral (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n : Fin 20) (g : (Fin 3 → ℝ) → ℝ) :
    (∫ z in C l n, g z) =
      ∫ u in delta, |(edgeMatrix l n).det| * g (cellPoint l n u) := by
  rw [← cellPoint_image]
  have hdet : ((edgeMatrix l n).mulVecLin.toContinuousLinearMap).det =
      (edgeMatrix l n).det := by
    rw [LinearMap.det_toContinuousLinearMap]
    exact LinearMap.det_toLin' _
  simpa only [hdet,smul_eq_mul] using
    integral_image_eq_integral_abs_det_fderiv_smul volume delta_compact.measurableSet
      (fun u _ => (cellPoint_hasFDerivAt l n u).hasFDerivWithinAt)
      (cellPoint_injective l hl n).injOn g

theorem actual_body_reference_integral (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i) :
    (∫ z in K l, originalDensity l z) =
      ∑ n : Fin 20, ∫ u in delta,
        |(edgeMatrix l n).det| * originalDensity l (cellPoint l n u) := by
  have hi : IntegrableOn (originalDensity l) (K l) := by
    exact CFMPNativeTwentyCellVolume435Transient.density_integrableOn l hl
  rw [CFMPTwentyCellIntegralAssembly435Transient.actual_body_integral l hl _ hi]
  exact Finset.sum_congr rfl (fun n _ => actual_cell_integral l hl n _)

end CFMPActualCellChangeVariables435Transient
