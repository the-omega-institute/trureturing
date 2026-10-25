import D5.S3.Geometry.Hyperideal.CFMPNativeFrameVelocity435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalFrameDensity435Transient
import D5.S3.Geometry.Hyperideal.CFMPAnchoredSmoothFrame435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalNativeCoordinates435Transient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Elementwise
open Filter
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPNativeFrameVelocity435Transient CFMPOriginalFrameDensity435Transient
open CFMPNativePullbackMetric435Transient CFMPOriginalNativeCoordinates435Transient
open CFMPAnchoredSmoothFrame435Transient
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace

namespace CFMPAnchoredFrameContinuity435Transient

theorem matrix_gram_rows (N : M4) (l : Fin 6 → ℝ)
    (hg : N * J * N.transpose = lengthGram l) (i j : Fin 4) :
    lorentz (N i) (N j) = lengthGram l i j := by
  calc
    _ = (N * J * N.transpose) i j := by
      simp [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.diagonal,
        Fin.sum_univ_four, lorentz]
      <;> ring
    _ = _ := congrFun (congrFun hg i) j

theorem anchored_original_motion
    (l0 : Fin 6 → ℝ) (hl0 : ∀ i, 0 < l0 i)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Fin 4 → ℝ, y = (radial l0 v.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (l : ℝ → (Fin 6 → ℝ)) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : HasDerivAt l dl t) (hbase : l t = l0)
    (x : CFMPFrameMotion435Transient.V) (hx : lift x ∈ cutBody l0) :
    let P : ℝ → M4 := fun s => frame M0 (l s)
    let D : M4 := (fderiv ℝ (frame M0) l0) dl
    P t = M0 ∧ HasDerivAt P D t ∧
      HasDerivAt (fun s => originalDensity (l s) x)
        (divergence (fun z => originalDensity l0 z • field (D * M0⁻¹) z) x) t ∧
      nativeMap (ambient (P t) x) = nativeCoordinates (f ⟨lift x,hx⟩) ∧
      deriv (fun s => nativeMap (ambient (P s) x)) t =
        deriv (fun r : ℝ => nativeMap
          (ambient M0 (x + r • field (D * M0⁻¹) x))) 0 := by
  let P : ℝ → M4 := fun s => frame M0 (l s)
  let D : M4 := (fderiv ℝ (frame M0) l0) dl
  have hgood : good (H M0 l0) := by
    rw [normalized_base M0 hm0 l0 hg0]
    exact base.2
  have hPbase : P t = M0 := by
    dsimp [P]
    rw [hbase,anchored M0 hm0 l0 hg0]
  have hdiff := (smooth_frame M0 l0 hgood).differentiableAt (by simp)
  have hdiff' : DifferentiableAt ℝ (frame M0) (l t) := by
    simpa only [hbase] using hdiff
  have hP : HasDerivAt P D t := by
    have h := hdiff'.hasFDerivAt.comp_hasDerivAt t hl
    simpa -implicitDefEqProofs only [P,D,hbase,Function.comp_def] using h
  have hcont : ContinuousAt (fun s => H M0 (l s)) t :=
    (smooth_H M0).continuous.continuousAt.comp hl.continuousAt
  have hgoodt : good (H M0 (l t)) := by simpa only [hbase] using hgood
  have hgoodEventually : ∀ᶠ s in 𝓝 t, good (H M0 (l s)) :=
    hcont.eventually (good_open.mem_nhds hgoodt)
  have hgram : ∀ᶠ s in 𝓝 t,
      ∀ i j, lorentz (P s i) (P s j) = lengthGram (l s) i j := by
    filter_upwards [hgoodEventually] with s hs
    exact matrix_gram_rows (P s) (l s) (frame_gram M0 hm0 (l s) hs)
  have hp := original_native_coordinates l0 hl0 M0 f hf ⟨lift x,hx⟩
  have hq : 0 < q (P t) x := by
    rw [hPbase]
    exact hp.1
  have hd : delta (ambient (P t) x) ≠ 0 := by
    rw [hPbase]
    exact hp.2.1.ne'
  have hdet : (P t).det ≠ 0 := by simpa only [hPbase] using hm0
  refine ⟨hPbase,hP,?_,?_,?_⟩
  · simpa only [hPbase,hbase] using
      original_density_continuity l P D x t hP hdet hgram hq.ne'
  · change nativeMap (ambient (P t) x) = _
    rw [hPbase]
    exact hp.2.2.symm
  · simpa only [hPbase] using
      original_native_motion_balance P D x t hP hdet hq hd

#print axioms anchored_original_motion
end CFMPAnchoredFrameContinuity435Transient
