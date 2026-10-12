/- GID: D5/S3/Geometry/Gluing/ActualLinkPathConnected
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/ActualLinkPathConnected
   mirror-E: none(waiver:actual-link-path-connected-frontier)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.PathConnected]
   utility: none
   digest: Full original actual-link vertex-class quotients are path connected. -/

import D5.S3.Geometry.Gluing.ActualLinkCornerChains
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
namespace D5.S3.Geometry.Gluing.ActualLinkPathConnected
open D5.S3.Geometry.Gluing.ActualLinkCornerChains
open D5.S3.Geometry.Hyperideal.ActualCornerTransport
open D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

/-- Every original vertex-class link is path connected in the quotient of the full
closed corner carrier. Tags have their discrete topology; coordinates have the
usual real product topology and the carrier and quotient have the induced and
quotient topologies. No transitivity or freeness of the right action is required. -/
theorem actual_link_path_connected [Fintype Ω] [TopologicalSpace Ω] [DiscreteTopology Ω]
    (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    PathConnectedSpace (Quotient (Relation.EqvGen.setoid (Step u v (ν := ν)))) := by
  classical
  let L := Quotient (Relation.EqvGen.setoid (Step u v (ν := ν)))
  let π : Point u v ν → L := Quotient.mk _
  have hπ : Continuous π := continuous_quotient_mk'
  -- Continuous paths stay in one complete closed triangle before descending.
  have same_tag (x y : Point u v ν) (htag : x.val.1 = y.val.1) :
      Joined (π x) (π y) := by
    let C : Set (Fin 4 → ℝ) :=
      {z | z x.val.1.2 = 0 ∧ (∀ i, 0 ≤ z i) ∧ (∑ i, z i) = 1}
    have hc : Convex ℝ C := by
      intro a ha b hb s t hs ht hst
      refine ⟨?_, ?_, ?_⟩
      · change s * a x.val.1.2 + t * b x.val.1.2 = 0
        rw [ha.1,hb.1,mul_zero,mul_zero,add_zero]
      · intro i
        exact add_nonneg (mul_nonneg hs (ha.2.1 i)) (mul_nonneg ht (hb.2.1 i))
      · change (∑ i : Fin 4, (s * a i + t * b i)) = 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ha.2.2,hb.2.2,mul_one,mul_one,hst]
    have hx : x.val.2 ∈ C := ⟨x.property.1,x.property.2.1,x.property.2.2.1⟩
    have hy : y.val.2 ∈ C := by
      exact ⟨by rw [htag]; exact y.property.1,y.property.2.1,y.property.2.2.1⟩
    let inclusion : C → Point u v ν := fun z =>
      ⟨(x.val.1,z.val),z.property.1,z.property.2.1,z.property.2.2,x.property.2.2.2⟩
    have hi : Continuous inclusion := by
      exact (continuous_const.prodMk continuous_subtype_val).subtype_mk _
    have h := ((hc.isPathConnected ⟨x.val.2,hx⟩).joinedIn _ hx _ hy).joined_subtype
    have hy' : inclusion ⟨y.val.2,hy⟩ = y := by
      apply Subtype.ext
      exact Prod.ext htag rfl
    simpa only [Function.comp_apply,hy'] using (h.map (hπ.comp hi))
  -- A vertex representative supplies a full triangle even when Ω was not assumed nonempty.
  have point_at (c : Corner Ω) (hc : label (pairing u v) c = ν) :
      ∃ x : Point u v ν, x.val.1 = c := by
    obtain ⟨k,hk⟩ : ∃ k : Fin 4, k ≠ c.2 := by
      generalize c.2 = j
      fin_cases j <;> decide
    refine ⟨⟨(c,fun i => if i = k then 1 else 0),?_,?_,?_,hc⟩,rfl⟩
    · change (if c.2 = k then (1 : ℝ) else 0) = 0
      simp [Ne.symm hk]
    · intro i
      change 0 ≤ (if i = k then (1 : ℝ) else 0)
      split_ifs <;> norm_num
    · simp
  -- The actual zero-guarded side is nonempty, and pairedPoint has the same quotient image.
  have across (i : Slot Ω) (x y : Point u v ν)
      (hx : x.val.1 = b i) (hy : y.val.1 = b (J (pairing u v) i)) :
      Joined (π x) (π y) := by
    rcases i with ⟨⟨ω,f⟩,r⟩
    let j := faceVertex f r
    have hfj : f ≠ j := by
      dsimp [j]
      fin_cases f <;> fin_cases r <;> decide
    obtain ⟨k,hkf,hkj⟩ : ∃ k : Fin 4, k ≠ f ∧ k ≠ j := by
      generalize j = j'
      fin_cases f <;> fin_cases j' <;> decide
    have hx' : x.val.1 = (ω,j) := by
      simpa [b, j] using hx
    have hlabel : label (pairing u v) (ω,j) = ν := by
      rw [← hx']
      exact x.property.2.2.2
    let z : Point u v ν := ⟨((ω,j),fun a => if a = k then 1 else 0),
      by
        change (if j = k then (1 : ℝ) else 0) = 0
        simp [Ne.symm hkj],
      by
        intro a
        change 0 ≤ (if a = k then (1 : ℝ) else 0)
        split_ifs <;> norm_num,
      by simp,hlabel⟩
    let w := pairedPoint u v z f hfj
    have hz : Step u v z w := ⟨f,hfj,by simp [z,Ne.symm hkf],rfl⟩
    have hw : w.val.1 = y.val.1 := by
      rw [hy]
      have hd := frozen_face_data u v ω f r
      change (act ω (faceWord u v f),facePerm f (faceVertex f r)) =
        ((facePair u v (ω,f)).1,
          faceVertex (facePair u v (ω,f)).2 (slotMap f r))
      rw [hd.1,hd.2]
    have he : π z = π w := Quotient.sound (Relation.EqvGen.rel _ _ hz)
    exact (same_tag x z hx).trans (by rw [he]; exact same_tag w y hw)
  have follows_joined (is : List (Slot Ω)) :
      ∀ (c d : Corner Ω), Follows (pairing u v) c d is →
      ∀ (x y : Point u v ν), x.val.1 = c → y.val.1 = d → Joined (π x) (π y) := by
    induction is with
    | nil =>
      intro c d h x y hx hy
      exact same_tag x y (hx.trans (h.trans hy.symm))
    | cons i is ih =>
      intro c d h x y hx hy
      have hnext : label (pairing u v) (b (J (pairing u v) i)) = ν := by
        have he : label (pairing u v) (b i) = label (pairing u v) (b (J (pairing u v) i)) :=
          Quotient.sound (Relation.EqvGen.rel _ _ ⟨i,rfl,rfl⟩)
        rw [← he,h.1,← hx]
        exact x.property.2.2.2
      obtain ⟨z,hz⟩ := point_at _ hnext
      exact (across i x z (hx.trans h.1.symm) hz).trans (ih _ _ h.2 z y hz hy)
  have all_joined (x y : Point u v ν) : Joined (π x) (π y) := by
    have ht := actual_corner_transport (pairing u v)
      (fun _ : Unit => x.val.1) (fun _ : Unit => y.val.1) (fun _ : Unit => (0 : ℝ))
      (fun _ => x.property.2.2.2.trans y.property.2.2.2.symm)
      (by intro _; exact le_rfl) 0 (by intro z; simp [mass])
    obtain ⟨paths,hpaths,_⟩ := ht
    exact follows_joined (paths ()) _ _ (hpaths ()) x y rfl rfl
  refine ⟨?_,?_⟩
  · obtain ⟨c,hc⟩ := Quotient.exists_rep ν
    obtain ⟨x,_⟩ := point_at c hc
    exact ⟨π x⟩
  · intro p q
    induction p using Quotient.inductionOn with
    | h x =>
      induction q using Quotient.inductionOn with
      | h y => exact all_joined x y


end D5.S3.Geometry.Gluing.ActualLinkPathConnected
