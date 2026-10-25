import D5.S3.Geometry.Hyperideal.CFMPAnchoredFrameContinuity435Transient
import D5.S3.Geometry.Hyperideal.CFMPActualPlaneIsometry435Transient
import D5.S3.Geometry.Hyperideal.CFMPActualPlaneBranch435Transient
import D5.S3.Geometry.HyperbolicPlaneRealization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators Topology Matrix.Norms.Elementwise
open Set Filter
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicPlaneRealization
open CFMPAnchoredSmoothFrame435Transient

namespace CFMPOriginalFutureFrame435Transient

def center : Fin 4 → ℝ := fun _ => 1/4

-- A finite bilinear expansion, used only inside this temporary exact application.
theorem frame_pair (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (u v : Fin 4 → ℝ) :
    lorentz (u ᵥ* M) (v ᵥ* M) = ∑ i, u i * ∑ j, lengthGram l i j * v j := by
  calc
    _ = ∑ k, ∑ i, ∑ j, u i * v j *
        ((![(1 : ℝ),1,1,-1] k) * M i k * M j k) := by
      simp only [lorentz, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, ∑ k, u i * v j *
        ((![(1 : ℝ),1,1,-1] k) * M i k * M j k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, u i * v j * lengthGram l i j := by
      simp_rw [← Finset.mul_sum]
      change (∑ i, ∑ j, u i * v j * lorentz (M i) (M j)) = _
      simp only [hG]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem radial_frame (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (v : Fin 4 → ℝ) :
    (radial l v) ᵥ* M = (Real.sqrt (-gramQuadratic l v))⁻¹ • (v ᵥ* M) := by
  have hr : radial l v = (Real.sqrt (-gramQuadratic l v))⁻¹ • v := by
    ext i
    simp [radial,div_eq_mul_inv,mul_comm]
  rw [hr,Matrix.smul_vecMul]

theorem center_pair_negative (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (v : cutBody l) : lorentz (v.val ᵥ* M) (center ᵥ* M) < 0 := by
  rw [frame_pair l M hG]
  have hr (i : Fin 4) : (∑ j, lengthGram l i j * center j) < 0 :=
    (shared_radial_body l hl).2.2.1 i
  obtain ⟨i,_,hi⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) => v.property.1.1 j)).mp
      (show (0 : ℝ) < ∑ j, v.val j by rw [v.property.1.2]; norm_num)
  calc
    _ < ∑ _j : Fin 4, (0 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro j _
        exact mul_nonpos_of_nonneg_of_nonpos (v.property.1.1 j) (hr j).le
      · exact ⟨i,Finset.mem_univ i,mul_neg_of_pos_of_neg hi (hr i)⟩
    _ = 0 := by simp

-- One future point fixes the sheet of every point of the original closed body.
theorem future_whole_body (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hcenter : 0 < (center ᵥ* M) 3) (v : cutBody l) :
    0 < ((radial l v.val) ᵥ* M) 3 ∧
      0 < ((radial l v.val) ᵥ* M) 3 - ((radial l v.val) ᵥ* M) 2 := by
  let b : cutBody l := ⟨center,(shared_radial_body l hl).2.1⟩
  have hs (w : cutBody l) : 0 < Real.sqrt (-gramQuadratic l w.val) :=
    Real.sqrt_pos.mpr (neg_pos.mpr ((shared_radial_body l hl).2.2.2.1 w.val w.property))
  have hu (w : cutBody l) :
      lorentz ((radial l w.val) ᵥ* M) ((radial l w.val) ᵥ* M) = -1 :=
    (CFMPActualPlaneIsometry435Transient.frame_quadratic l M hG _).trans
      ((shared_radial_body l hl).2.2.2.2.2.2.2.2.1 w.val w.property)
  have hb : 0 < ((radial l b.val) ᵥ* M) 3 := by
    rw [radial_frame]
    exact mul_pos (inv_pos.mpr (hs b)) hcenter
  have hp : lorentz ((radial l b.val) ᵥ* M) ((radial l v.val) ᵥ* M) < 0 := by
    rw [radial_frame,radial_frame]
    have he : lorentz
        ((Real.sqrt (-gramQuadratic l b.val))⁻¹ • (b.val ᵥ* M))
        ((Real.sqrt (-gramQuadratic l v.val))⁻¹ • (v.val ᵥ* M)) =
        ((Real.sqrt (-gramQuadratic l b.val))⁻¹ *
          (Real.sqrt (-gramQuadratic l v.val))⁻¹) *
            lorentz (v.val ᵥ* M) (b.val ᵥ* M) := by
      simp only [lorentz,Fin.sum_univ_four,Pi.smul_apply,smul_eq_mul]
      ring
    rw [he]
    exact mul_neg_of_pos_of_neg
      (mul_pos (inv_pos.mpr (hs b)) (inv_pos.mpr (hs v)))
      (center_pair_negative l hl M hG v)
  have ht := D5.S3.Geometry.HyperbolicPlaneRealization.positive_time_of_pair
    _ _ (hu b) (hu v) hb hp
  exact ⟨ht,future_den _ (hu v) ht⟩

theorem anchored_future_neighborhood
    (l0 : Fin 6 → ℝ) (hl0 : ∀ i, 0 < l0 i)
    (M0 : Matrix (Fin 4) (Fin 4) ℝ) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2))) :
    ∀ᶠ l in 𝓝 l0, (∀ i, 0 < l i) ∧ (frame M0 l).det ≠ 0 ∧
      (∀ i j, lorentz (frame M0 l i) (frame M0 l j) = lengthGram l i j) ∧
      ∀ v : cutBody l,
        0 < ((radial l v.val) ᵥ* frame M0 l) 3 ∧
        0 < ((radial l v.val) ᵥ* frame M0 l) 3 -
          ((radial l v.val) ᵥ* frame M0 l) 2 := by
  have hb : center ∈ cutBody l0 := (shared_radial_body l0 hl0).2.1
  have hs : 0 < Real.sqrt (-gramQuadratic l0 center) :=
    Real.sqrt_pos.mpr (neg_pos.mpr ((shared_radial_body l0 hl0).2.2.2.1 center hb))
  obtain ⟨y,hy,_,ht,_⟩ := hf ⟨center,hb⟩
  have ht0 : 0 < (center ᵥ* M0) 3 := by
    rw [hy,radial_frame] at ht
    exact pos_of_mul_pos_right ht (inv_pos.mpr hs).le
  have hg : good (H M0 l0) := by
    rw [normalized_base M0 hm0 l0 hg0]
    exact base.2
  have hc : ContinuousAt (fun l => (center ᵥ* frame M0 l) 3) l0 := by
    change ContinuousAt (fun l => ∑ i, center i * frame M0 l i 3) l0
    refine tendsto_finsetSum Finset.univ fun i _ => ?_
    exact continuousAt_const.mul
      ((continuous_apply 3).continuousAt.comp ((continuous_apply i).continuousAt.comp
        (smooth_frame M0 l0 hg).continuousAt))
  have hct : 0 < (center ᵥ* frame M0 l0) 3 := by
    rw [anchored M0 hm0 l0 hg0]
    exact ht0
  have he := hc.eventually (Ioi_mem_nhds hct)
  obtain ⟨V,hV,hmem,hpos,_,_,hGram⟩ := local_original_frame M0 hm0 l0 hl0 hg0
  have hgood := (smooth_H M0).continuous.continuousAt.eventually
    (good_open.mem_nhds hg)
  filter_upwards [he,hV.mem_nhds hmem,hgood] with l hc hV hgood
  have hr := CFMPAnchoredFrameContinuity435Transient.matrix_gram_rows
    (frame M0 l) l (hGram l hV)
  exact ⟨hpos l hV,frame_det_nonzero M0 hm0 l hgood,hr,
    fun v => future_whole_body l (hpos l hV) (frame M0 l) hr hc v⟩

end CFMPOriginalFutureFrame435Transient
