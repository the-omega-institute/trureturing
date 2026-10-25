import D5.S3.Geometry.Hyperideal.CFMPFrameAffineTransport435Transient
import D5.S3.Geometry.Hyperideal.CFMPActualNativeCellMotion435Transient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Elementwise
open Filter
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPFrameAffineTransport435Transient CFMPActualCellMotion435Transient
open CFMPActualNativeCellMotion435Transient CFMPOriginalCellsIndependent435Transient
open CFMPOriginalFrameDensity435Transient CFMPOriginalNativeCoordinates435Transient
open CFMPAnchoredSmoothFrame435Transient
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace

namespace CFMPOriginalCellTransport435Transient

theorem original_cell_transport
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
    let D : M4 := (fderiv ℝ (frame M0) l0) dl
    let o : ℝ → (Fin 3 → ℝ) := fun s => drop (vertices (l s) n 0)
    let B : ℝ → M3 := fun s => edgeMatrix (l s) n
    let v := deriv o t
    let E := deriv B t
    HasDerivAt
      (fun s => |(edgeMatrix (l s) n).det| * originalDensity (l s) (cellPoint (l s) n u))
      (divergence (totalFlux M0 (D*M0⁻¹) (edgeMatrix l0 n) E
        (drop (vertices l0 n 0)) v) u) t := by
  let P : ℝ → M4 := fun s => frame M0 (l s)
  let D : M4 := (fderiv ℝ (frame M0) l0) dl
  let o : ℝ → (Fin 3 → ℝ) := fun s => drop (vertices (l s) n 0)
  let B : ℝ → M3 := fun s => edgeMatrix (l s) n
  let v := deriv o t
  let E := deriv B t
  let x := cellPoint l0 n u
  have hx := lift_cellPoint_mem_body l0 hl0 n u hu
  have ha := CFMPAnchoredFrameContinuity435Transient.anchored_original_motion
    l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase x hx
  have hPt : P t = M0 := ha.1
  have hP : HasDerivAt P D t := ha.2.1
  have hB : HasDerivAt B E t :=
    (edgeMatrix_differentiable l t hl.differentiableAt n).hasDerivAt
  have ho : HasDerivAt o v t := by
    apply DifferentiableAt.hasDerivAt
    apply differentiableAt_pi.mpr
    intro i
    exact differentiableAt_pi.mp (vertices_differentiable l t hl.differentiableAt n 0) i.castSucc
  have hdetP : (P t).det ≠ 0 := by simpa only [hPt] using hm0
  have hdetB : (B t).det ≠ 0 := by
    simpa only [B,hbase] using edgeMatrix_det_ne_zero l0 hl0 n
  have hxt : o t+(B t).mulVec u = x := by simp only [o,B,x,cellPoint,hbase]
  have hq : q (P t) (o t+(B t).mulVec u) ≠ 0 := by
    rw [hPt,hxt]
    exact (original_native_coordinates l0 hl0 M0 f hf ⟨lift x,hx⟩).1.ne'
  have ht := frame_affine_transport P D o B v u E t hP ho
    (fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hB i) j) hdetP hdetB hq
  have hgood : good (H M0 l0) := by
    rw [normalized_base M0 hm0 l0 hg0]
    exact base.2
  have hcont : ContinuousAt (fun s => H M0 (l s)) t :=
    (smooth_H M0).continuous.continuousAt.comp hl.continuousAt
  have hgoodt : good (H M0 (l t)) := by simpa only [hbase] using hgood
  have hgoodEventually : ∀ᶠ s in 𝓝 t, good (H M0 (l s)) :=
    hcont.eventually (good_open.mem_nhds hgoodt)
  have heq : ∀ᶠ s in 𝓝 t,
      |(edgeMatrix (l s) n).det| * originalDensity (l s) (cellPoint (l s) n u) =
        |(B s).det| * density (P s) (o s+(B s).mulVec u) := by
    filter_upwards [hgoodEventually] with s hs
    have hg := CFMPAnchoredFrameContinuity435Transient.matrix_gram_rows
      (P s) (l s) (frame_gram M0 hm0 (l s) hs)
    rw [density_eq_original (P s) (l s) hg]
    rfl
  have h := ht.congr_of_eventuallyEq heq
  simpa only [hPt,B,o,hbase] using h

#print axioms original_cell_transport
end CFMPOriginalCellTransport435Transient
