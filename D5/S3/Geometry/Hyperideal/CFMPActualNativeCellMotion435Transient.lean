import D5.S3.Geometry.Hyperideal.CFMPActualCellMotion435Transient
import D5.S3.Geometry.Hyperideal.CFMPCellIntersections435Transient
import D5.S3.Geometry.Hyperideal.CFMPAnchoredFrameContinuity435Transient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Elementwise
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPActualCellMotion435Transient
open CFMPOriginalCellsIndependent435Transient
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPNativePullbackMetric435Transient CFMPOriginalNativeCoordinates435Transient
open CFMPAnchoredSmoothFrame435Transient

namespace CFMPActualNativeCellMotion435Transient

def referenceSimplex (u : Fin 3 → ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ (∑ i, u i) ≤ 1

def weights (u : Fin 3 → ℝ) : Fin 4 → ℝ := Fin.cons (1-∑ i, u i) u

def coefficientPoint (l : Fin 6 → ℝ) (n : Fin 20) (u : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ∑ j, weights u j • vertices l n j

theorem weights_nonnegative (u : Fin 3 → ℝ) (hu : referenceSimplex u) (j : Fin 4) :
    0 ≤ weights u j := by
  cases j using Fin.cases with
  | zero => simpa [weights] using sub_nonneg.mpr hu.2
  | succ j => simpa [weights] using hu.1 j

theorem weights_sum (u : Fin 3 → ℝ) : (∑ j, weights u j) = 1 := by
  simp [weights, Fin.sum_univ_succ]

theorem coefficientPoint_mem_body (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n : Fin 20) (u : Fin 3 → ℝ) (hu : referenceSimplex u) :
    coefficientPoint l n u ∈ cutBody l := by
  have hc : Convex ℝ (cutBody l) := by
    rw [← (cut_body_polytope l hl).2.1]
    exact convex_convexHull ℝ _
  exact hc.sum_mem (fun j _ => weights_nonnegative u hu j) (weights_sum u)
    (fun j _ => CFMPCellIntersections435Transient.vertex_mem_body l hl n j)

theorem drop_coefficientPoint (l : Fin 6 → ℝ) (n : Fin 20) (u : Fin 3 → ℝ) :
    drop (coefficientPoint l n u) = cellPoint l n u := by
  ext i
  simp [coefficientPoint, weights, drop, cellPoint, edgeMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, Fin.sum_univ_three, smul_eq_mul]
  ring

theorem lift_cellPoint (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n : Fin 20) (u : Fin 3 → ℝ) (hu : referenceSimplex u) :
    CFMPFrameMotion435Transient.lift (cellPoint l n u) = coefficientPoint l n u := by
  change liftAffine (cellPoint l n u) = coefficientPoint l n u
  rw [← drop_coefficientPoint]
  exact CFMPOriginalCellsIndependent435Transient.lift_drop _
    (coefficientPoint_mem_body l hl n u hu).1.2

theorem lift_cellPoint_mem_body (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n : Fin 20) (u : Fin 3 → ℝ) (hu : referenceSimplex u) :
    CFMPFrameMotion435Transient.lift (cellPoint l n u) ∈ cutBody l := by
  rw [lift_cellPoint l hl n u hu]
  exact coefficientPoint_mem_body l hl n u hu

theorem anchored_actual_cell_motion
    (l0 : Fin 6 → ℝ) (hl0 : ∀ i, 0 < l0 i)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (l : ℝ → (Fin 6 → ℝ)) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : HasDerivAt l dl t) (hbase : l t = l0)
    (n : Fin 20) (u : Fin 3 → ℝ) (hu : referenceSimplex u) :
    let P : ℝ → M4 := fun s => frame M0 (l s)
    let D : M4 := (fderiv ℝ (frame M0) l0) dl
    let x := cellPoint l0 n u
    let v := deriv (fun s => cellPoint (l s) n u) t
    (edgeMatrix l0 n).det ≠ 0 ∧
      nativeMap (ambient M0 x) = nativeCoordinates
        (f ⟨CFMPFrameMotion435Transient.lift x, lift_cellPoint_mem_body l0 hl0 n u hu⟩) ∧
      deriv (fun s => nativeMap (ambient (P s) (cellPoint (l s) n u))) t =
        deriv (fun r : ℝ => nativeMap
          (ambient M0 (x+r • (v+field (D*M0⁻¹) x)))) 0 := by
  let P : ℝ → M4 := fun s => frame M0 (l s)
  let D : M4 := (fderiv ℝ (frame M0) l0) dl
  let x := cellPoint l0 n u
  let v := deriv (fun s => cellPoint (l s) n u) t
  have hx := lift_cellPoint_mem_body l0 hl0 n u hu
  have hanchor := CFMPAnchoredFrameContinuity435Transient.anchored_original_motion
    l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase x hx
  rcases hanchor with ⟨hPbase,hP,hcontinuity,hnative,hfixed⟩
  have hPt : P t = M0 := hPbase
  have hxt : cellPoint (l t) n u = x := by simp only [hbase,x]
  have hp := original_native_coordinates l0 hl0 M0 f hf
    ⟨CFMPFrameMotion435Transient.lift x,hx⟩
  have hq : 0 < q (P t) (cellPoint (l t) n u) := by
    rw [hxt,hPt]
    exact hp.1
  have hd : delta (ambient (P t) (cellPoint (l t) n u)) ≠ 0 := by
    rw [hxt,hPt]
    exact hp.2.1.ne'
  have hdet : (P t).det ≠ 0 := by simpa only [hPt] using hm0
  have hpath : HasDerivAt (fun s => cellPoint (l s) n u) v t :=
    (cellPoint_differentiable l t hl.differentiableAt n u).hasDerivAt
  refine ⟨edgeMatrix_det_ne_zero l0 hl0 n,?_,?_⟩
  · simpa only [hPbase] using hnative
  · simpa only [hPt,hxt] using
      CFMPNativeMovingPoint435Transient.total_native_velocity P D
        (fun s => cellPoint (l s) n u) v t hP hpath hdet hq hd

#print axioms anchored_actual_cell_motion
end CFMPActualNativeCellMotion435Transient
