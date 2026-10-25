import D5.S3.Geometry.Hyperideal.CFMPOriginalAnchoredRealization435Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Elementwise
open Set Filter
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPAnchoredSmoothFrame435Transient
open CFMPOriginalFutureFrame435Transient
open CFMPOriginalAnchoredRealization435Transient

namespace CFMPOriginalAnchoredFamily435Transient

-- The length domain is fixed and open; each body fiber remains its original subtype.
theorem exists_original_anchored_family
    (l0 : Fin 6 → ℝ) (hl0 : ∀ i, 0 < l0 i)
    (M0 : Matrix (Fin 4) (Fin 4) ℝ) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2))) :
    ∃ (U : Set (Fin 6 → ℝ)) (h0 : l0 ∈ U)
      (g : ∀ a : U, cutBody a.val → HyperbolicThreeSpace),
      IsOpen U ∧ ContDiffOn ℝ ∞ (frame M0) U ∧ frame M0 l0 = M0 ∧
      g ⟨l0,h0⟩ = f ∧
      ∀ a : U, (∀ i, 0 < a.val i) ∧ (frame M0 a.val).det ≠ 0 ∧
        (∀ i j, lorentz (frame M0 a.val i) (frame M0 a.val j) = lengthGram a.val i j) ∧
        Continuous (g a) ∧ Function.Injective (g a) ∧ IsCompact (range (g a)) ∧
        ∀ w : cutBody a.val, ∃ y : Fin 4 → ℝ,
          y = (radial a.val w.val) ᵥ* frame M0 a.val ∧
          lorentz y y = -1 ∧ 0 < y 3 ∧
          (g a w).coordinates.val = WithLp.toLp 2
            (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)) := by
  have hnear := anchored_future_neighborhood l0 hl0 M0 hm0 hg0 f hf
  have hg : good (H M0 l0) := by
    rw [normalized_base M0 hm0 l0 hg0]
    exact base.2
  have hgood := (smooth_H M0).continuous.continuousAt.eventually
    (good_open.mem_nhds hg)
  obtain ⟨U,hsub,hopen,h0⟩ := mem_nhds_iff.mp (hnear.and hgood)
  have hp (a : U) := hsub a.property
  have hcenter (a : U) : 0 < (center ᵥ* frame M0 a.val) 3 := by
    have hb : CFMPOriginalFutureFrame435Transient.center ∈ cutBody a.val := (shared_radial_body a.val (hp a).1.1).2.1
    have ht := ((hp a).1.2.2.2 ⟨center,hb⟩).1
    rw [radial_frame] at ht
    have hs : 0 < Real.sqrt (-gramQuadratic a.val center) :=
      Real.sqrt_pos.mpr (neg_pos.mpr
        ((shared_radial_body a.val (hp a).1.1).2.2.2.1 center hb))
    exact pos_of_mul_pos_right ht (inv_pos.mpr hs).le
  let g : ∀ a : U, cutBody a.val → HyperbolicThreeSpace := fun a =>
    realize a.val (hp a).1.1 (frame M0 a.val) (hp a).1.2.2.1 (hcenter a)
  have hanchor := anchored M0 hm0 l0 hg0
  have hbase : g ⟨l0,h0⟩ = f := by
    dsimp only [g]
    apply realize_eq_original
    intro w
    simpa only [hanchor] using hf w
  refine ⟨U,h0,g,hopen,?_,hanchor,hbase,?_⟩
  · intro a ha
    exact (smooth_frame M0 a (hp ⟨a,ha⟩).2).contDiffWithinAt
  · intro a
    refine ⟨(hp a).1.1,(hp a).1.2.1,(hp a).1.2.2.1,?_,?_,?_,?_⟩
    · exact realize_continuous a.val (hp a).1.1 (frame M0 a.val)
        (hp a).1.2.2.1 (hcenter a)
    · exact realize_injective a.val (hp a).1.1 (frame M0 a.val) (hp a).1.2.1
        (hp a).1.2.2.1 (hcenter a)
    · exact realize_compact a.val (hp a).1.1 (frame M0 a.val)
        (hp a).1.2.2.1 (hcenter a)
    · intro w
      exact realize_contract a.val (hp a).1.1 (frame M0 a.val)
        (hp a).1.2.2.1 (hcenter a) w

end CFMPOriginalAnchoredFamily435Transient
