/- GID: D5/S3/Topology/StableCategory/ColourGraphJoin
   generality: G
   mirror-B: none(waiver:support-for-the-tetrahedral-refinement)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A pair of properly coloured graphs gives rank charts on their join. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.FiniteSimplicialJoin
import D5.S3.Topology.OrdinaryCollarRetraction
import D5.S3.Topology.StableCategory.OrdinaryContiguityLift
import D5.S3.Topology.OrdinarySubdivisionMap
import Mathlib.Data.Finset.Sum

/-! The graph join combines the two colours of a simplicial factorization. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.ColourGraphJoin

open D5.S3.Geometry.FiniteSimplicialJoin (simplicialJoin)
open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (sd)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryContiguityLift (Simplicial ofTotal of_total_simplicial)
open private image from D5.S3.Topology.OrdinarySubdivisionMap

noncomputable section

local instance (priority := 2000) (V : Type*) : DecidableEq V := Classical.decEq V

variable {X U V : Type}
variable {K : PreAbstractSimplicialComplex X}
variable {G : PreAbstractSimplicialComplex U} {H : PreAbstractSimplicialComplex V}

/-- The two Boolean colours on the tagged vertices of a simplicial join. -/
def leftColour : U ⊕ V → Bool := Sum.elim (fun _ => true) (fun _ => false)

def rightColour : U ⊕ V → Bool := Sum.elim (fun _ => false) (fun _ => true)

private theorem toLeft_image_inl (s : Finset U) :
    (image s (Sum.inl : U → U ⊕ V)).toLeft = s := by
  ext u
  simp [image]

private theorem toRight_image_inl (s : Finset U) :
    (image s (Sum.inl : U → U ⊕ V)).toRight = ∅ := by
  ext v
  simp [image]

private theorem toLeft_image_inr (s : Finset V) :
    (image s (Sum.inr : V → U ⊕ V)).toLeft = ∅ := by
  ext u
  simp [image]

private theorem toRight_image_inr (s : Finset V) :
    (image s (Sum.inr : V → U ⊕ V)).toRight = s := by
  ext v
  simp [image]

private theorem project_inl_image (u₀ : U) (s : Finset U) :
    image (s.map (Function.Embedding.inl : U ↪ U ⊕ V)) (Sum.elim id (fun _ => u₀)) = s := by
  ext x
  simp [image, Finset.mem_map]

private theorem project_inr_image (v₀ : V) (s : Finset V) :
    image (s.map (Function.Embedding.inr : V ↪ U ⊕ V)) (Sum.elim (fun _ => v₀) id) = s := by
  ext x
  simp [image, Finset.mem_map]

/-- The left colour cut of the join contains exactly the tagged left faces. -/
theorem left_colourComplex_image (s : Finset U) (hs : s ∈ G) :
    image s Sum.inl ∈ colourComplex (simplicialJoin G H) leftColour := by
  refine ⟨?_, ?_⟩
  · refine ⟨Finset.image_nonempty.mpr (G.isRelLowerSet_faces hs).1, ?_, ?_⟩
    · rw [toLeft_image_inl]
      exact Or.inr hs
    · rw [toRight_image_inl]
      exact Or.inl rfl
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    simp [leftColour]

theorem right_colourComplex_image (s : Finset V) (hs : s ∈ H) :
    image s Sum.inr ∈ colourComplex (simplicialJoin G H) rightColour := by
  refine ⟨?_, ?_⟩
  · refine ⟨Finset.image_nonempty.mpr (H.isRelLowerSet_faces hs).1, ?_, ?_⟩
    · rw [toLeft_image_inr]
      exact Or.inl rfl
    · rw [toRight_image_inr]
      exact Or.inr hs
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    simp [rightColour]

private theorem left_projection_image (u₀ : U) (s : Finset (U ⊕ V))
    (hs : s ∈ colourComplex (simplicialJoin G H) leftColour) :
    image s (Sum.elim id (fun _ => u₀)) ∈ G := by
  have hs' : s ∈ simplicialJoin G H ∧ ∀ x ∈ s, leftColour x = true := hs
  have hright : s.toRight = ∅ := by
    ext v
    rw [Finset.mem_toRight]
    constructor
    · intro hv
      have hc := hs'.2 (Sum.inr v) hv
      simp [leftColour] at hc
    · intro hv
      exact (Finset.notMem_empty v hv).elim
  have hsmap : s = s.toLeft.map Function.Embedding.inl := by
    calc
      s = s.toLeft.disjSum s.toRight :=
        (Finset.toLeft_disjSum_toRight (u := s)).symm
      _ = s.toLeft.map Function.Embedding.inl := by rw [hright, Finset.disjSum_empty]
  have hleft : s.toLeft ∈ G := by
    rcases hs'.1.2.1 with hempty | hG
    · have : s.toLeft ≠ ∅ := by
        intro he
        have : s = ∅ := by rw [hsmap, he, Finset.map_empty]
        simpa [this] using hs'.1.1
      exact (this hempty).elim
    · exact hG
  rw [hsmap]
  rw [project_inl_image]
  exact hleft

private theorem right_projection_image (v₀ : V) (s : Finset (U ⊕ V))
    (hs : s ∈ colourComplex (simplicialJoin G H) rightColour) :
    image s (Sum.elim (fun _ => v₀) id) ∈ H := by
  have hs' : s ∈ simplicialJoin G H ∧ ∀ x ∈ s, rightColour x = true := hs
  have hleft : s.toLeft = ∅ := by
    ext u
    rw [Finset.mem_toLeft]
    constructor
    · intro hu
      have hc := hs'.2 (Sum.inl u) hu
      simp [rightColour] at hc
    · intro hu
      exact (Finset.notMem_empty u hu).elim
  have hsmap : s = s.toRight.map Function.Embedding.inr := by
    calc
      s = s.toLeft.disjSum s.toRight :=
        (Finset.toLeft_disjSum_toRight (u := s)).symm
      _ = s.toRight.map Function.Embedding.inr := by rw [hleft, Finset.empty_disjSum]
  have hright : s.toRight ∈ H := by
    rcases hs'.1.2.2 with hempty | hH
    · have : s.toRight ≠ ∅ := by
        intro he
        have : s = ∅ := by rw [hsmap, he, Finset.map_empty]
        simpa [this] using hs'.1.1
      exact (this hempty).elim
    · exact hH
  rw [hsmap]
  rw [project_inr_image]
  exact hright

def leftJoinMap : Vertex G → Vertex (colourComplex (simplicialJoin G H) leftColour) :=
  ofTotal Sum.inl left_colourComplex_image

def rightJoinMap : Vertex H → Vertex (colourComplex (simplicialJoin G H) rightColour) :=
  ofTotal Sum.inr right_colourComplex_image

/-- Combine two vertex maps defined on the two colour classes. -/
def joinMap (colour : X → Bool) (left : X → U) (right : X → V) : X → U ⊕ V :=
  fun x => if colour x then Sum.inl (left x) else Sum.inr (right x)

/-- Simplicial maps on the two induced colour subcomplexes combine to a
colour-preserving map into the simplicial join. -/
theorem join_map_image (colour : X → Bool) (left : X → U) (right : X → V)
    (hl : ∀ s ∈ colourComplex K colour, image s left ∈ G)
    (hr : ∀ s ∈ colourComplex K (fun x => !colour x), image s right ∈ H) :
    ∀ s ∈ K, image s (joinMap colour left right) ∈ simplicialJoin G H := by
  intro s hs
  let a := s.filter (fun x => colour x = true)
  let b := s.filter (fun x => (!colour x) = true)
  let t := image s (joinMap colour left right)
  have hleft : t.toLeft = image a left := by
    ext u
    rw [Finset.mem_toLeft, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, he⟩
      cases hxColour : colour x with
      | false => simp [joinMap, hxColour] at he
      | true => exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxColour⟩, Sum.inl.inj (by
          simpa only [joinMap, hxColour, Bool.true_eq, ite_true] using he)⟩
    · rintro ⟨x, hx, rfl⟩
      have hx' := Finset.mem_filter.mp hx
      exact ⟨x, hx'.1, by simp [joinMap, hx'.2]⟩
  have hright : t.toRight = image b right := by
    ext v
    rw [Finset.mem_toRight, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, he⟩
      cases hxColour : colour x with
      | true => simp [joinMap, hxColour] at he
      | false => exact ⟨x, Finset.mem_filter.mpr ⟨hx, by simp [hxColour]⟩,
          Sum.inr.inj (by simpa only [joinMap, hxColour, Bool.false_eq_true, ite_false] using he)⟩
    · rintro ⟨x, hx, rfl⟩
      have hx' := Finset.mem_filter.mp hx
      have hfalse : colour x = false := by
        have hn := hx'.2
        cases h : colour x <;> simp_all
      exact ⟨x, hx'.1, by simp [joinMap, hfalse]⟩
  refine ⟨(K.isRelLowerSet_faces hs).1.image _, ?_, ?_⟩
  · rw [hleft]
    by_cases h : a.Nonempty
    · exact Or.inr (hl a ⟨(K.isRelLowerSet_faces hs).2 (Finset.filter_subset _ _) h,
        fun _ hx => (Finset.mem_filter.mp hx).2⟩)
    · exact Or.inl (by simp [Finset.not_nonempty_iff_eq_empty.mp h])
  · rw [hright]
    by_cases h : b.Nonempty
    · exact Or.inr (hr b ⟨(K.isRelLowerSet_faces hs).2 (Finset.filter_subset _ _) h,
        fun _ hx => (Finset.mem_filter.mp hx).2⟩)
    · exact Or.inl (by simp [Finset.not_nonempty_iff_eq_empty.mp h])

/-- Two bipartite graph colourings give four proper ranks on their join. -/
def joinRank (p : U → Fin 2) (q : V → Fin 2) : U ⊕ V → Fin 4 :=
  Sum.elim (fun x => ⟨(p x).val, (p x).isLt.trans (Nat.lt_succ_of_le (by decide))⟩)
    (fun y => ⟨2 + (q y).val, Nat.add_lt_add_left (q y).isLt 2⟩)

theorem join_rank_proper (p : U → Fin 2) (q : V → Fin 2)
    (hp : ∀ s ∈ G, Set.InjOn p (s : Set U)) (hq : ∀ s ∈ H, Set.InjOn q (s : Set V)) :
    ∀ s ∈ simplicialJoin G H, Set.InjOn (joinRank p q) (s : Set (U ⊕ V)) := by
  intro s hs a ha b hb hab
  have hl : s.toLeft = ∅ ∨ s.toLeft ∈ G := hs.2.1
  have hr : s.toRight = ∅ ∨ s.toRight ∈ H := hs.2.2
  have hval := congrArg Fin.val hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have ha' : a ∈ s.toLeft := Finset.mem_toLeft.mpr ha
      have hb' : b ∈ s.toLeft := Finset.mem_toLeft.mpr hb
      rcases hl with ht | ht
      · rw [ht] at ha'
        exact (Finset.notMem_empty a ha').elim
      · exact congrArg Sum.inl (hp _ ht ha' hb' (Fin.ext hval))
    | inr b =>
      have ht : (p a).val < 2 := (p a).isLt
      change (p a).val = 2 + (q b).val at hval
      rw [hval] at ht
      exact (not_lt_of_ge (Nat.le_add_right 2 _)) ht |>.elim
  | inr a =>
    cases b with
    | inl b =>
      have ht : (p b).val < 2 := (p b).isLt
      change 2 + (q a).val = (p b).val at hval
      rw [← hval] at ht
      exact (not_lt_of_ge (Nat.le_add_right 2 _)) ht |>.elim
    | inr b =>
      have ha' : a ∈ s.toRight := Finset.mem_toRight.mpr ha
      have hb' : b ∈ s.toRight := Finset.mem_toRight.mpr hb
      rcases hr with ht | ht
      · rw [ht] at ha'
        exact (Finset.notMem_empty a ha').elim
      · exact congrArg Sum.inr (hq _ ht ha' hb' (Fin.ext (Nat.add_left_cancel hval)))

/-- Face size gives a proper rank colouring of an ordinary subdivision,
with as many ranks as the largest original face has vertices. -/
theorem subdivision_rank_colouring (A : PreAbstractSimplicialComplex X) {n : ℕ}
    (hcard : ∀ s ∈ A, (s : Finset X).card ≤ n) :
    (∀ s ∈ sd A, (s : Finset (Face A)).card ≤ n) ∧
      ∃ rank : Face A → Fin n, ∀ s ∈ sd A, Set.InjOn rank (s : Set (Face A)) := by
  let rank (a : Face A) : Fin n :=
    ⟨a.val.card - 1, by
      have hpos := Finset.card_pos.mpr (A.isRelLowerSet_faces a.property).1
      have hle := hcard _ a.property
      exact (Nat.sub_lt hpos (Nat.zero_lt_succ 0)).trans_le hle⟩
  have mass (a : Face A) : (rank a).val + 1 = a.val.card :=
    Nat.sub_add_cancel (Finset.card_pos.mpr (A.isRelLowerSet_faces a.property).1)
  have proper (s : Finset (Face A)) (hs : s ∈ sd A) :
      Set.InjOn rank (s : Set (Face A)) := by
    intro a ha b hb h
    by_contra hn
    have he : a.val.card = b.val.card :=
      (mass a).symm.trans ((congrArg (fun j : Fin n => j.val + 1) h).trans (mass b))
    rcases hs.2.1 ha hb hn with hlt | hlt
    · exact (Finset.card_lt_card hlt).ne he
    · exact (Finset.card_lt_card hlt).ne he.symm
  refine ⟨fun s hs => ?_, ⟨rank, proper⟩⟩
  rw [← Finset.card_image_of_injOn (proper s hs)]
  exact (Finset.card_le_univ _).trans (by simp)

end

end D5.S3.Topology.StableCategory.ColourGraphJoin
