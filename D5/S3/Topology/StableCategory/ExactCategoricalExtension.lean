/- GID: D5/S3/Topology/StableCategory/ExactCategoricalExtension
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/ExactCategoricalExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Categorical extensions in an ordinary subdivision with exact old intersections. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.FourPieceCategoricalCover
import D5.S3.Topology.StableCategory.OrdinaryCollarContiguity
import D5.S3.Topology.StableCategory.OrdinaryContiguityLift

/-! # Exact retention after an ordinary subdivision

The ambient complex is fixed before both old and extended pieces are
subdivided. The same projection to the old vertex set gives the old pieces
in the three-piece extension and the first piece in the two-piece extension.
The input can already be at a common inherited subdivision depth.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.ExactCategoricalExtension

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous sd vertexOfFace)
open BarycentricNeighborhoodIteration (FullIn subdivision subdivision_full)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryContiguityLift (Simplicial includeSubcomplex include_subcomplex_simplicial
  comp_chains subdivide lift_chain)
open Relation (ReflTransGen)
open private vertexIn mapCollar descending_collar_maps map_collar_simplicial
  from D5.S3.Topology.StableCategory.OrdinaryCollarContiguity
open private face_image_include constant_simplicial id_simplicial restrictFlag
  restrictFlag_simplicial subdivision_const
  from D5.S3.Topology.StableCategory.FourPieceCategoricalCover

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X
attribute [local instance] Classical.propDecidable

variable {V : Type} {S T U C A : PreAbstractSimplicialComplex V}

/-- An inclusion is categorical when a finite contiguity chain in its ambient
complex joins it to a constant vertex map. -/
abbrev CategoricalIn (h : A ≤ S) : Prop :=
  ∃ c : Vertex S, ReflTransGen Contiguous (includeSubcomplex h) (fun _ => c)

/-- Intersect a face with the vertex set of the retained complex. -/
private def oldPart (T : PreAbstractSimplicialComplex V) (a : Finset V) : Finset V :=
  a.filter fun v => ({v} : Finset V) ∈ T

private theorem oldPart_mono (T : PreAbstractSimplicialComplex V) {a b : Finset V}
    (hab : a ⊆ b) : oldPart T a ⊆ oldPart T b :=
  Finset.filter_subset_filter _ hab

private theorem oldPart_eq {a : Finset V} (ha : a ∈ T) : oldPart T a = a := by
  apply Finset.filter_true_of_mem
  intro v hv
  exact (T.isRelLowerSet_faces ha).2
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)

private theorem old_le_oldPart {q a : Finset V} (hq : q ∈ T) (hqa : q ⊆ a) :
    q ⊆ oldPart T a := by
  simpa only [oldPart_eq hq] using oldPart_mono T hqa

private theorem oldPart_mem (hT : FullIn T S) (a : Face S)
    (hne : (oldPart T a.val).Nonempty) : oldPart T a.val ∈ T := by
  refine hT.2 ⟨oldPart T a.val,
    (S.isRelLowerSet_faces a.property).2 (Finset.filter_subset _ _) hne⟩ ?_
  intro v hv
  exact (Finset.mem_filter.mp hv).2

private def projectedPiece (S T C : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex (Face S) :=
  colourComplex (sd S) fun a => decide (oldPart T a.val ∈ C)

private theorem projectedPiece_le (S T C : PreAbstractSimplicialComplex V) :
    projectedPiece S T C ≤ sd S :=
  fun _ hs => hs.1

private theorem projectedPiece_restrict (hC : C ≤ T) :
    projectedPiece S T C ⊓ subdivision S T = subdivision S C := by
  apply le_antisymm
  · intro s hs
    have hp : s ∈ projectedPiece S T C := hs.1
    have ht : s ∈ subdivision S T := hs.2
    refine ⟨ht.1, ht.2.1, fun a ha => ?_⟩
    have he : oldPart T a.val ∈ C := of_decide_eq_true (hp.2 a ha)
    rwa [oldPart_eq (ht.2.2 a ha)] at he
  · intro s hs
    refine ⟨⟨⟨hs.1, hs.2.1, fun a _ => a.property⟩, ?_⟩,
      ⟨hs.1, hs.2.1, fun a ha => hC (hs.2.2 a ha)⟩⟩
    intro a ha
    apply decide_eq_true
    rw [oldPart_eq (hC (hs.2.2 a ha))]
    exact hs.2.2 a ha

/-- A restriction of the simplicial contraction of an ordinary subdivision
can be composed with a contiguity chain from a new piece's inclusion. -/
private theorem categorical_of_subdivision_factor [Finite V]
    {Y : PreAbstractSimplicialComplex (Face S)}
    (hY : Y ≤ sd S) (hA : A ≤ S) (hcat : CategoricalIn hA)
    (f : Vertex Y → Vertex (sd A)) (hf : Simplicial f)
    (hchain : ReflTransGen Contiguous (includeSubcomplex hY)
      (subdivide (includeSubcomplex hA) (include_subcomplex_simplicial hA) ∘ f)) :
    CategoricalIn hY := by
  obtain ⟨c, hc⟩ := hcat
  have hlift := lift_chain (include_subcomplex_simplicial hA)
    (constant_simplicial (K := A) c) hc
  have hcomp := comp_chains f id hf (id_simplicial (K := sd S)) hlift
  rw [Function.id_comp, Function.id_comp, subdivision_const] at hcomp
  exact ⟨_, hchain.trans hcomp⟩

private theorem categorical_of_subdivision_le [Finite V]
    {Y : PreAbstractSimplicialComplex (Face S)}
    (hY : Y ≤ subdivision S A) (hA : A ≤ S) (hcat : CategoricalIn hA) :
    CategoricalIn (hY.trans (subdivision_full S A).1) := by
  let keep := restrictFlag S A ∘ includeSubcomplex hY
  have hkeep : Simplicial keep :=
    (restrictFlag_simplicial S A).comp (include_subcomplex_simplicial hY)
  have hstart : subdivide (includeSubcomplex hA) (include_subcomplex_simplicial hA) ∘ keep =
      includeSubcomplex (hY.trans (subdivision_full S A).1) := by
    funext v
    apply Subtype.ext
    apply Subtype.ext
    exact face_image_include hA v.val.val (keep v).val.property
  refine categorical_of_subdivision_factor _ hA hcat keep hkeep ?_
  rw [hstart] <;> exact .refl

private theorem projectedPiece_categorical [Finite V]
    (hC : C ≤ S) (hcat : CategoricalIn hC) :
    CategoricalIn (projectedPiece_le S T C) := by
  let p (a : Face S) := decide (oldPart T a.val ∈ C)
  let cut : {a : Face S // p a = true} →o Face C :=
    ⟨fun a => ⟨oldPart T a.val.val, of_decide_eq_true a.property⟩,
      fun _ _ h => oldPart_mono T h⟩
  let inc : {a : Face S // p a = true} →o Face S := ⟨Subtype.val, fun _ _ h => h⟩
  let into : {a : Face S // p a = true} →o Face S :=
    (show Face C →o Face S from ⟨fun a => ⟨a.val, hC a.property⟩, fun _ _ h => h⟩).comp cut
  have hchain := descending_collar_maps p inc into (fun _ => Finset.filter_subset _ _)
  have hcut : Simplicial (mapCollar p cut) := by
    intro s hs
    simpa only [Finset.union_idempotent] using map_collar_simplicial p cut s hs
  have hstart : mapCollar p inc = includeSubcomplex (projectedPiece_le S T C) := by
    funext v
    exact Subtype.ext rfl
  have hend : mapCollar p into =
      subdivide (includeSubcomplex hC) (include_subcomplex_simplicial hC) ∘ mapCollar p cut := by
    funext v
    apply Subtype.ext
    apply Subtype.ext
    exact (face_image_include hC (cut (vertexIn v)).val (cut (vertexIn v)).property).symm
  rw [hstart, hend] at hchain
  exact categorical_of_subdivision_factor _ hC hcat _ hcut hchain

private theorem flag_comparable {s : Finset (Face S)} (hs : s ∈ sd S)
    {a b : Face S} (ha : a ∈ s) (hb : b ∈ s) : a ≤ b ∨ b ≤ a := by
  by_cases he : a = b
  · exact Or.inl he.le
  · exact (hs.2.1 ha hb he).imp LT.lt.le LT.lt.le

private theorem flag_top {s : Finset (Face S)} (hs : s ∈ sd S) :
    ∃ m ∈ s, ∀ a ∈ s, a ≤ m := by
  obtain ⟨a, ha⟩ := hs.1
  obtain ⟨m, _, hm⟩ := Finset.exists_le_maximal s ha
  refine ⟨m, hm.1, fun a ha => ?_⟩
  rcases flag_comparable hs ha hm.1 with ham | hma
  · exact ham
  · exact hm.2 ha hma

private theorem flag_subdivision_of_top {s : Finset (Face S)} (hs : s ∈ sd S)
    {m : Face S} (htop : ∀ a ∈ s, a ≤ m) (hmA : m.val ∈ A) :
    s ∈ subdivision S A :=
  ⟨hs.1, hs.2.1, fun a ha =>
    (A.isRelLowerSet_faces hmA).2 (htop a ha) (S.isRelLowerSet_faces a.property).1⟩

private theorem in_projectedPiece_of_old_vertex {s : Finset (Face S)} (hs : s ∈ sd S)
    {q m : Face S} (hq : q ∈ s) (hqT : q.val ∈ T)
    (htop : ∀ a ∈ s, a ≤ m) (hmC : oldPart T m.val ∈ C) :
    s ∈ projectedPiece S T C := by
  refine ⟨hs, fun a ha => decide_eq_true ((C.isRelLowerSet_faces hmC).2
    (oldPart_mono T (htop a ha)) ?_)⟩
  rcases flag_comparable hs hq ha with hqa | haq
  · exact (T.isRelLowerSet_faces hqT).1.mono (old_le_oldPart hqT hqa)
  · have haT := (T.isRelLowerSet_faces hqT).2 haq (S.isRelLowerSet_faces a.property).1
    rw [oldPart_eq haT]
    exact (T.isRelLowerSet_faces haT).1

private theorem subdivision_mono (S : PreAbstractSimplicialComplex V) (h : A ≤ C) :
    subdivision S A ≤ subdivision S C :=
  fun _ hs => ⟨hs.1, hs.2.1, fun a ha => h (hs.2.2 a ha)⟩

/-- A flag in the attachment whose actual old faces all belong to `C`. -/
private def attachmentPiece (S T U C : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex (Face S) :=
  colourComplex (subdivision S U) fun a => decide (a.val ∈ T → a.val ∈ C)

private theorem attachmentPiece_le (S T U C : PreAbstractSimplicialComplex V) :
    attachmentPiece S T U C ≤ subdivision S U :=
  fun _ hs => hs.1

private theorem attachmentPiece_restrict_le :
    attachmentPiece S T U C ⊓ subdivision S T ≤ subdivision S C := by
  intro s hs
  have hp : s ∈ attachmentPiece S T U C := hs.1
  have ht : s ∈ subdivision S T := hs.2
  refine ⟨ht.1, ht.2.1, fun a ha => ?_⟩
  have h : a.val ∈ T → a.val ∈ C := of_decide_eq_true (hp.2 a ha)
  exact h (ht.2.2 a ha)

private theorem secondPiece_restrict (hC : C ≤ T) :
    (subdivision S C ⊔ attachmentPiece S T U C) ⊓ subdivision S T = subdivision S C := by
  apply le_antisymm
  · intro s hs
    rcases hs.1 with hc | hu
    · exact hc
    · exact attachmentPiece_restrict_le (S := S) (T := T) (U := U) (C := C) ⟨hu, hs.2⟩
  · exact le_inf le_sup_left (subdivision_mono S hC)

private theorem no_old_faces :
    attachmentPiece S T U ⊥ ⊓ subdivision S T = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro s hs
  have h : s ∈ subdivision S ⊥ := attachmentPiece_restrict_le hs
  obtain ⟨a, ha⟩ := h.1
  have he : False := h.2.2 a ha
  exact he.elim

private theorem mem_union_cases (hS : S = T ⊔ U) {a : Finset V} (ha : a ∈ S) :
    a ∈ T ∨ a ∈ U := by
  change a ∈ T ⊔ U
  rwa [← hS]

/-- An asymmetric categorical two-cover extends after one ordinary
subdivision when the second old piece and the attachment are categorical
together. Both old intersections are exact inside the same ambient subdivision. -/
theorem exact_two_piece_extension [Finite V] {C0 C1 : PreAbstractSimplicialComplex V}
    (hS : S = T ⊔ U) (hT : FullIn T S) (hCover : T = C0 ⊔ C1)
    (hC0 : C0 ≤ S) (hC1U : C1 ⊔ U ≤ S)
    (hcat0 : CategoricalIn hC0) (hcat1U : CategoricalIn hC1U) :
    ∃ Y0 Y1 : PreAbstractSimplicialComplex (Face S),
      ∃ hY0 : Y0 ≤ sd S, ∃ hY1 : Y1 ≤ sd S,
        sd S = Y0 ⊔ Y1 ∧
        Y0 ⊓ subdivision S T = subdivision S C0 ∧
        Y1 ⊓ subdivision S T = subdivision S C1 ∧
        CategoricalIn hY0 ∧ CategoricalIn hY1 := by
  have hC0T : C0 ≤ T := by
    rw [hCover]
    exact le_sup_left
  have hC1T : C1 ≤ T := by
    rw [hCover]
    exact le_sup_right
  let Y0 := projectedPiece S T C0
  let Y1 := subdivision S C1 ⊔ attachmentPiece S T U C1
  have hY0 : Y0 ≤ sd S := projectedPiece_le S T C0
  have hY1sub : Y1 ≤ subdivision S (C1 ⊔ U) :=
    sup_le (subdivision_mono S le_sup_left)
      ((attachmentPiece_le S T U C1).trans (subdivision_mono S le_sup_right))
  have hY1 : Y1 ≤ sd S := hY1sub.trans (subdivision_full S (C1 ⊔ U)).1
  refine ⟨Y0, Y1, hY0, hY1, ?_, projectedPiece_restrict hC0T,
    secondPiece_restrict hC1T, projectedPiece_categorical hC0 hcat0,
    categorical_of_subdivision_le hY1sub hC1U hcat1U⟩
  refine le_antisymm ?_ (sup_le hY0 hY1)
  intro s hs
  by_cases h0 : s ∈ Y0
  · exact Or.inl h0
  apply Or.inr
  obtain ⟨m, hm, htop⟩ := flag_top hs
  have old_in_C1 (q : Face S) (hq : q ∈ s) (hqT : q.val ∈ T) : q.val ∈ C1 := by
    by_contra hq1
    have hqproj : q.val ⊆ oldPart T m.val := old_le_oldPart hqT (htop q hq)
    have hqne := (T.isRelLowerSet_faces hqT).1
    have hprojT := oldPart_mem hT m (hqne.mono hqproj)
    have hproj0 := (mem_union_cases hCover hprojT).resolve_right fun hproj1 =>
      hq1 ((C1.isRelLowerSet_faces hproj1).2 hqproj hqne)
    exact h0 (in_projectedPiece_of_old_vertex hs hq hqT htop hproj0)
  by_cases hmT : m.val ∈ T
  · exact Or.inl (flag_subdivision_of_top hs htop (old_in_C1 m hm hmT))
  · have hmU := (mem_union_cases hS m.property).resolve_left hmT
    exact Or.inr ⟨flag_subdivision_of_top hs htop hmU,
      fun q hq => decide_eq_true (old_in_C1 q hq)⟩

/-- When the two old pieces and the attachment are separately categorical,
one ordinary subdivision gives an exact extension with three pieces. The
third piece is disjoint from the subdivided retained complex. -/
theorem exact_three_piece_extension [Finite V] {C0 C1 : PreAbstractSimplicialComplex V}
    (hS : S = T ⊔ U) (hT : FullIn T S) (hCover : T = C0 ⊔ C1)
    (hC0 : C0 ≤ S) (hC1 : C1 ≤ S) (hU : U ≤ S)
    (hcat0 : CategoricalIn hC0) (hcat1 : CategoricalIn hC1) (hcatU : CategoricalIn hU) :
    ∃ Y0 Y1 Y2 : PreAbstractSimplicialComplex (Face S),
      ∃ hY0 : Y0 ≤ sd S, ∃ hY1 : Y1 ≤ sd S, ∃ hY2 : Y2 ≤ sd S,
        sd S = (Y0 ⊔ Y1) ⊔ Y2 ∧
        Y0 ⊓ subdivision S T = subdivision S C0 ∧
        Y1 ⊓ subdivision S T = subdivision S C1 ∧
        Y2 ⊓ subdivision S T = ⊥ ∧
        CategoricalIn hY0 ∧ CategoricalIn hY1 ∧ CategoricalIn hY2 := by
  have hC0T : C0 ≤ T := by
    rw [hCover]
    exact le_sup_left
  have hC1T : C1 ≤ T := by
    rw [hCover]
    exact le_sup_right
  let Y0 := projectedPiece S T C0
  let Y1 := projectedPiece S T C1
  let Y2 := attachmentPiece S T U ⊥
  have hY0 : Y0 ≤ sd S := projectedPiece_le S T C0
  have hY1 : Y1 ≤ sd S := projectedPiece_le S T C1
  have hY2sub : Y2 ≤ subdivision S U := attachmentPiece_le S T U ⊥
  have hY2 : Y2 ≤ sd S := hY2sub.trans (subdivision_full S U).1
  refine ⟨Y0, Y1, Y2, hY0, hY1, hY2, ?_, projectedPiece_restrict hC0T,
    projectedPiece_restrict hC1T, no_old_faces, projectedPiece_categorical hC0 hcat0,
    projectedPiece_categorical hC1 hcat1, categorical_of_subdivision_le hY2sub hU hcatU⟩
  refine le_antisymm ?_ (sup_le (sup_le hY0 hY1) hY2)
  intro s hs
  obtain ⟨m, hm, htop⟩ := flag_top hs
  by_cases old : ∃ q ∈ s, q.val ∈ T
  · obtain ⟨q, hq, hqT⟩ := old
    have hqproj : q.val ⊆ oldPart T m.val := old_le_oldPart hqT (htop q hq)
    have hprojT := oldPart_mem hT m ((T.isRelLowerSet_faces hqT).1.mono hqproj)
    rcases mem_union_cases hCover hprojT with hproj0 | hproj1
    · exact Or.inl (Or.inl (in_projectedPiece_of_old_vertex hs hq hqT htop hproj0))
    · exact Or.inl (Or.inr (in_projectedPiece_of_old_vertex hs hq hqT htop hproj1))
  · have hmU := (mem_union_cases hS m.property).resolve_left (fun hmT => old ⟨m, hm, hmT⟩)
    exact Or.inr ⟨flag_subdivision_of_top hs htop hmU,
      fun q hq => decide_eq_true (fun hqT => (old ⟨q, hq, hqT⟩).elim)⟩

/-- A full categorical cover that contains the prescribed old pieces yields
an exact extension after one ordinary subdivision. -/
theorem exact_extension_of_full_cover [Finite V] {I : Type}
    (C Z : I → PreAbstractSimplicialComplex V)
    (hC : ∀ i, C i ≤ T) (hCZ : ∀ i, C i ≤ Z i)
    (hZ : ∀ i, FullIn (Z i) S)
    (oldCover : ∀ s ∈ T, ∃ i, s ∈ C i)
    (cover : ∀ s ∈ S, ∃ i, s ∈ Z i)
    (categorical : ∀ i, CategoricalIn (hZ i).1) :
    ∃ Y : I → PreAbstractSimplicialComplex (Face S), ∃ hY : ∀ i, Y i ≤ sd S,
      (∀ s ∈ sd S, ∃ i, s ∈ Y i) ∧
      (∀ i, Y i ⊓ subdivision S T = subdivision S (C i)) ∧
      (∀ i, CategoricalIn (hY i)) := by
  let Y (i : I) := projectedPiece S (Z i) (Z i) ⊓
    colourComplex (sd S) (fun a => decide (a.val ∈ T → a.val ∈ C i))
  have hproj (i : I) : Y i ≤ projectedPiece S (Z i) (Z i) := inf_le_left
  have hY (i : I) : Y i ≤ sd S := (hproj i).trans (projectedPiece_le S _ _)
  refine ⟨Y, hY, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨m, _, hm⟩ := flag_top hs
    by_cases hold : ∃ q ∈ s, q.val ∈ T
    · obtain ⟨q, hq, hqT⟩ := hold
      let old := s.filter fun a => a.val ∈ T
      obtain ⟨b, hb⟩ := old.exists_maximal ⟨q, Finset.mem_filter.mpr ⟨hq, hqT⟩⟩
      have hb' := Finset.mem_filter.mp hb.1
      obtain ⟨i, hi⟩ := oldCover b.val hb'.2
      have hbZ := hCZ i hi
      have hpart := oldPart_mem (hZ i) m
        (((Z i).isRelLowerSet_faces hbZ).1.mono (old_le_oldPart hbZ (hm b hb'.1)))
      refine ⟨i, in_projectedPiece_of_old_vertex hs hb'.1 hbZ hm hpart, hs, ?_⟩
      intro a ha
      apply decide_eq_true
      intro haT
      have hab := (flag_comparable hs ha hb'.1).elim id
        (hb.2 (Finset.mem_filter.mpr ⟨ha, haT⟩))
      exact ((C i).isRelLowerSet_faces hi).2 hab (S.isRelLowerSet_faces a.property).1
    · obtain ⟨b, hb⟩ := s.exists_minimal hs.1
      obtain ⟨i, hi⟩ := cover b.val b.property
      have hpart := oldPart_mem (hZ i) m
        (((Z i).isRelLowerSet_faces hi).1.mono (old_le_oldPart hi (hm b hb.1)))
      refine ⟨i, in_projectedPiece_of_old_vertex hs hb.1 hi hm hpart, hs, ?_⟩
      intro a ha
      exact decide_eq_true (fun haT => (hold ⟨a, ha, haT⟩).elim)
  · intro i
    apply le_antisymm
    · intro s hs
      have ht : s ∈ subdivision S T := hs.2
      have hp := (show s ∈ Y i from hs.1).2
      exact ⟨ht.1, ht.2.1, fun a ha =>
        (of_decide_eq_true (hp.2 a ha) : a.val ∈ T → a.val ∈ C i) (ht.2.2 a ha)⟩
    · intro s hs
      have hz := subdivision_mono S (hCZ i) hs
      have ht := subdivision_mono S (hC i) hs
      have hp : s ∈ projectedPiece S (Z i) (Z i) := by
        refine ⟨(subdivision_full S (Z i)).1 hz, fun a ha => ?_⟩
        apply decide_eq_true
        rw [oldPart_eq (hz.2.2 a ha)]
        exact hz.2.2 a ha
      exact ⟨⟨hp, (subdivision_full S T).1 ht,
        fun a ha => decide_eq_true (fun _ => hs.2.2 a ha)⟩, ht⟩
  · intro i
    obtain ⟨c, hc⟩ := projectedPiece_categorical (T := Z i) (hZ i).1 (categorical i)
    have h := comp_chains (includeSubcomplex (hproj i)) id
      (include_subcomplex_simplicial (hproj i)) (id_simplicial (K := sd S)) hc
    exact ⟨c, h⟩

end
end D5.S3.Topology.StableCategory.ExactCategoricalExtension
