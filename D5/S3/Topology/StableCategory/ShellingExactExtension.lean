/- GID: D5/S3/Topology/StableCategory/ShellingExactExtension
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/ShellingExactExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A categorical cover extends with exact restrictions across a shelling simplex. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.DepthZeroElementaryExpansion
import D5.S3.Topology.StableCategory.MixedSimplexAttachment

/-! Exact categorical extensions across one simplex attached along a union of facets. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.ExactCategoricalExtension

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (sd)
open BarycentricNeighborhoodIteration (FullIn subdivision subdivision_full)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryContiguityLift (includeSubcomplex include_subcomplex_simplicial comp_chains)
open private id_simplicial from
  D5.S3.Topology.StableCategory.FourPieceCategoricalCover
open private oldPart oldPart_mem oldPart_eq old_le_oldPart projectedPiece projectedPiece_le
  projectedPiece_categorical flag_top flag_comparable
  in_projectedPiece_of_old_vertex subdivision_mono from
  D5.S3.Topology.StableCategory.ExactCategoricalExtension

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X
attribute [local instance] Classical.propDecidable

variable {V : Type} {S T : PreAbstractSimplicialComplex V}

/-- A cover by full categorical regions needs only to cover the ambient vertices. -/
theorem exact_extension_of_vertex_cover [Finite V] {I : Type}
    (C Z : I → PreAbstractSimplicialComplex V)
    (hC : ∀ i, C i ≤ T) (hCZ : ∀ i, C i ≤ Z i)
    (hZ : ∀ i, FullIn (Z i) S)
    (oldCover : ∀ s ∈ T, ∃ i, s ∈ C i)
    (cover : ∀ v : Vertex S, ∃ i, ({v.val} : Finset V) ∈ Z i)
    (categorical : ∀ i, CategoricalIn (hZ i).1) :
    ∃ Y : I → PreAbstractSimplicialComplex (Face S), ∃ hY : ∀ i, FullIn (Y i) (sd S),
      (∀ s ∈ sd S, ∃ i, s ∈ Y i) ∧
      (∀ i, Y i ⊓ subdivision S T = subdivision S (C i)) ∧
      (∀ i, CategoricalIn (hY i).1) := by
  let Y (i : I) := projectedPiece S (Z i) (Z i) ⊓
    colourComplex (sd S) (fun a => decide (a.val ∈ T → a.val ∈ C i))
  have hproj (i : I) : Y i ≤ projectedPiece S (Z i) (Z i) := inf_le_left
  have hY (i : I) : FullIn (Y i) (sd S) := by
    refine ⟨(hproj i).trans (projectedPiece_le S _ _), fun s hs => ?_⟩
    refine ⟨⟨s.property, ?_⟩, ⟨s.property, ?_⟩⟩
    · intro a ha
      exact (hs a ha).1.2 a (Finset.mem_singleton_self a)
    · intro a ha
      exact (hs a ha).2.2 a (Finset.mem_singleton_self a)
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
      obtain ⟨v, hv⟩ := (S.isRelLowerSet_faces b.property).1
      have hvs : ({v} : Finset V) ⊆ b.val := Finset.singleton_subset_iff.mpr hv
      let w : Vertex S :=
        ⟨v, (S.isRelLowerSet_faces b.property).2 hvs (Finset.singleton_nonempty v)⟩
      obtain ⟨i, hi⟩ := cover w
      have hle : ∀ a ∈ s, b ≤ a := by
        intro a ha
        exact (flag_comparable hs hb.1 ha).elim id (hb.2 ha)
      have hp (a : Face S) (ha : a ∈ s) : oldPart (Z i) a.val ∈ Z i :=
        oldPart_mem (hZ i) a ((Finset.singleton_nonempty v).mono
          (old_le_oldPart hi (hvs.trans (hle a ha))))
      refine ⟨i, ⟨hs, fun a ha => decide_eq_true (hp a ha)⟩, hs, ?_⟩
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

namespace D5.S3.Topology.StableCategory.ShellingExactExtension

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous sd skeleton vertexOfFace)
open BarycentricNeighborhoodIteration
  (FullIn subdivision subdivision_full iteratedAmbient iteratedSubcomplex)
open ExactCategoricalExtension (CategoricalIn exact_extension_of_vertex_cover)
open GraphSubdivisionIntervals (mem_iteratedSubcomplex_iff originalSupport)
open MixedSimplexChart (simplex)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryContiguityLift (Simplicial includeSubcomplex include_subcomplex_simplicial
  comp_chains constant_chain_of_reachable)
open DisjointContiguityGluing (glue_contiguity)
open Relation (ReflTransGen)
open D5.S3.Geometry.FiniteElementaryCollapse (CollapsePair)
open private bisect_walk incident_face_walk from
  D5.S3.Topology.BarycentricBaseRigidity
open private categorical_of_subdivision_le categorical_of_subdivision_factor
  flag_comparable flag_top flag_subdivision_of_top subdivision_mono mem_union_cases from
  D5.S3.Topology.StableCategory.ExactCategoricalExtension
open private d2_le d2_sup from D5.S3.Topology.StableCategory.MixedSimplexAttachment
open private vertexIn mapCollar descending_collar_maps map_collar_simplicial collar_chain_symm
  from D5.S3.Topology.StableCategory.OrdinaryCollarContiguity
open private face_image_include constant_simplicial id_simplicial
  from D5.S3.Topology.StableCategory.FourPieceCategoricalCover
open private colourPiece from D5.S3.Topology.StableCategory.DisjointContiguityGluing

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X
attribute [local instance] Classical.propDecidable

variable {V : Type} {K A P P₀ P₁ : PreAbstractSimplicialComplex V}
variable {σ J : Finset V}

private abbrev D2 (K P : PreAbstractSimplicialComplex V) := iteratedSubcomplex K P 2

private abbrev FlagRegion (K : PreAbstractSimplicialComplex V) (p : Face (sd K) → Bool) :=
  colourComplex (sd (sd K)) p

private abbrev Allowed (K : PreAbstractSimplicialComplex V) (p : Face (sd K) → Bool) :=
  {q : Face (sd K) // p q = true}

private theorem region_full (p : Face (sd K) → Bool) :
    FullIn (FlagRegion K p) (sd (sd K)) := by
  refine ⟨fun _ hs => hs.1, fun q h => ⟨q.property, ?_⟩⟩
  intro a ha
  exact (h a ha).2 a (Finset.mem_singleton_self a)

private theorem region_vertex {p : Face (sd K) → Bool} {q : Face (sd K)} :
    ({q} : Finset (Face (sd K))) ∈ FlagRegion K p ↔ p q = true := by
  constructor
  · exact fun h => h.2 q (Finset.mem_singleton_self q)
  · intro h
    refine ⟨(vertexOfFace (sd K) q).property, ?_⟩
    intro r hr
    rwa [Finset.mem_singleton.mp hr]

private theorem region_restrict {p : Face (sd K) → Bool} (hPA : P ≤ A)
    (hp : ∀ q : Face (sd K), q.val ∈ subdivision K A →
      (p q = true ↔ q.val ∈ subdivision K P)) :
    FlagRegion K p ⊓ D2 K A = D2 K P := by
  apply le_antisymm
  · intro s hs
    refine ⟨hs.2.1, hs.2.2.1, fun q hq => ?_⟩
    exact (hp q (hs.2.2.2 q hq)).mp (hs.1.2 q hq)
  · intro s hs
    have ha := d2_le K hPA hs
    exact ⟨⟨(subdivision_full (sd K) (subdivision K P)).1 hs,
      fun q hq => (hp q (ha.2.2 q hq)).mpr (hs.2.2 q hq)⟩, ha⟩

private def incOrder (p : Face (sd K) → Bool) : Allowed K p →o Face (sd K) :=
  ⟨Subtype.val, fun _ _ h => h⟩

private theorem incOrder_map (p : Face (sd K) → Bool) :
    mapCollar p (incOrder p) = includeSubcomplex (region_full p).1 := by
  funext v
  exact Subtype.ext rfl

private def filterOrder (p : Face (sd K) → Bool) (keep : Face K → Prop)
    (hne : ∀ q : Allowed K p, (q.val.val.filter keep).Nonempty) :
    Allowed K p →o Face (sd K) where
  toFun q := ⟨q.val.val.filter keep,
    (PreAbstractSimplicialComplex.isRelLowerSet_faces _ q.val.property).2
      (Finset.filter_subset _ _) (hne q)⟩
  monotone' := fun _ _ h => Finset.filter_subset_filter _ h

private theorem flag_insert (q : Face (sd K)) (t : Face K)
    (h : ∀ a ∈ q.val, t ≤ a ∨ a ≤ t) : insert t q.val ∈ sd K := by
  refine ⟨Finset.insert_nonempty _ _, ?_, fun a _ => a.property⟩
  intro a ha b hb hab
  change a ∈ insert t q.val at ha
  change b ∈ insert t q.val at hb
  by_cases ha' : a = t
  · subst a
    have hb' := (Finset.mem_insert.mp hb).resolve_left hab.symm
    exact (h b hb').imp (fun ht => lt_of_le_of_ne ht hab)
      (fun ht => lt_of_le_of_ne ht hab.symm)
  · have haq := (Finset.mem_insert.mp ha).resolve_left ha'
    by_cases hb' : b = t
    · subst b
      exact (h a haq).symm.imp (fun ht => lt_of_le_of_ne ht hab)
        (fun ht => lt_of_le_of_ne ht hab.symm)
    · exact q.property.2.1 haq ((Finset.mem_insert.mp hb).resolve_left hb') hab

private theorem categorical_of_flag_factor [Finite V] {p : Face (sd K) → Bool}
    (hPK : P ≤ K) (hcat : CategoricalIn hPK)
    (r : Allowed K p →o Face (sd K))
    (hr : ∀ q, (r q).val ∈ subdivision K P)
    (hc : ReflTransGen Contiguous (mapCollar p (incOrder p)) (mapCollar p r)) :
    CategoricalIn (region_full p).1 := by
  let r' : Allowed K p →o Face (subdivision K P) :=
    ⟨fun q => ⟨(r q).val, hr q⟩, fun _ _ h => r.monotone h⟩
  have hsimp : Simplicial (mapCollar p r') := by
    intro s hs
    simpa only [Finset.union_idempotent] using map_collar_simplicial p r' s hs
  have he : mapCollar p r = OrdinaryContiguityLift.subdivide
      (includeSubcomplex (subdivision_full K P).1)
      (include_subcomplex_simplicial (subdivision_full K P).1) ∘ mapCollar p r' := by
    funext v
    apply Subtype.ext
    apply Subtype.ext
    exact (face_image_include (subdivision_full K P).1
      (r' (vertexIn v)).val (r' (vertexIn v)).property).symm
  rw [incOrder_map, he] at hc
  exact categorical_of_subdivision_factor _ (subdivision_full K P).1
    (categorical_of_subdivision_le (le_refl (subdivision K P)) hPK hcat) _ hsimp hc

private theorem cut_categorical [Finite V] {p : Face (sd K) → Bool}
    (hPK : P ≤ K) (hcat : CategoricalIn hPK)
    (hmeets : ∀ q : Allowed K p, ∃ a ∈ q.val.val, a.val ∈ P) :
    CategoricalIn (region_full p).1 := by
  have hne (q : Allowed K p) : (q.val.val.filter fun a => a.val ∈ P).Nonempty := by
    obtain ⟨a, ha, hP⟩ := hmeets q
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, hP⟩⟩
  let r := filterOrder p (fun a => a.val ∈ P) hne
  refine categorical_of_flag_factor hPK hcat r (fun q => ⟨(r q).property.1,
    (r q).property.2.1, fun a ha => (Finset.mem_filter.mp ha).2⟩) ?_
  exact descending_collar_maps p (incOrder p) r (fun _ => Finset.filter_subset _ _)

private def oldOrMeeting (A P : PreAbstractSimplicialComplex V) (q : Face (sd K)) : Prop :=
  if q.val ∈ subdivision K A then q.val ∈ subdivision K P
  else ∃ a ∈ q.val, a.val ∈ P

private theorem oldOrMeeting_categorical [Finite V] (hPK : P ≤ K)
    (hcat : CategoricalIn hPK) :
    CategoricalIn (region_full (K := K) (fun q => decide (oldOrMeeting A P q))).1 := by
  refine cut_categorical (p := fun q => decide (oldOrMeeting A P q)) hPK hcat ?_
  intro q
  have hp : oldOrMeeting A P q.val := of_decide_eq_true q.property
  by_cases hq : q.val.val ∈ subdivision K A
  · have hP : q.val.val ∈ subdivision K P := by
      simpa only [oldOrMeeting, ite_eq_left hq] using hp
    obtain ⟨a, ha⟩ := hP.1
    exact ⟨a, ha, hP.2.2 a ha⟩
  · simpa only [oldOrMeeting, ite_eq_right hq] using hp

private def anchored (A P : PreAbstractSimplicialComplex V) (t : Face K)
    (q : Face (sd K)) : Prop :=
  if q.val ∈ subdivision K A then q.val ∈ subdivision K P
  else ∀ a ∈ q.val, t ≤ a ∧ (a.val ∈ A → a.val ∈ P)

private theorem anchored_categorical [Finite V] (hPK : P ≤ K) (hcat : CategoricalIn hPK)
    (t : Face K) (ht : t.val ∈ P) :
    CategoricalIn (region_full (fun q => decide (anchored A P t q))).1 := by
  let p (q : Face (sd K)) := decide (anchored A P t q)
  have old_keep (q : Allowed K p) (hq : q.val.val ∈ subdivision K A) :
      q.val.val ∈ subdivision K P := by
    have hh : anchored A P t q.val := of_decide_eq_true q.property
    simpa only [anchored, ite_eq_left hq] using hh
  have new_keep (q : Allowed K p) (hq : q.val.val ∉ subdivision K A) :
      ∀ a ∈ q.val.val, t ≤ a ∧ (a.val ∈ A → a.val ∈ P) := by
    have hh : anchored A P t q.val := of_decide_eq_true q.property
    simpa only [anchored, ite_eq_right hq] using hh
  have insert_mem (q : Allowed K p) (hq : q.val.val ∉ subdivision K A) :
      insert t q.val.val ∈ sd K :=
    flag_insert q.val t (fun a ha => Or.inl (new_keep q hq a ha).1)
  let adjoin : Allowed K p →o Face (sd K) := by
    refine ⟨fun q => if hq : q.val.val ∈ subdivision K A then q.val else
      ⟨insert t q.val.val, insert_mem q hq⟩, ?_⟩
    intro q u h
    change (if hq : q.val.val ∈ subdivision K A then q.val else
      ⟨insert t q.val.val, insert_mem q hq⟩) ≤
        (if hu : u.val.val ∈ subdivision K A then u.val else
          ⟨insert t u.val.val, insert_mem u hu⟩)
    have hle : q.val.val ⊆ u.val.val := h
    by_cases hu : u.val.val ∈ subdivision K A
    · have hq : q.val.val ∈ subdivision K A :=
        ((subdivision K A).isRelLowerSet_faces hu).2 hle q.val.property.1
      rw [dite_eq_left hu, dite_eq_left hq]
      exact h
    · rw [dite_eq_right hu]
      by_cases hq : q.val.val ∈ subdivision K A
      · rw [dite_eq_left hq]
        exact hle.trans (Finset.subset_insert _ _)
      · rw [dite_eq_right hq]
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (h hx)
  let trim : Allowed K p →o Face (sd K) := by
    refine ⟨fun q => ⟨(adjoin q).val.filter (fun a => a.val ∈ P),
      (PreAbstractSimplicialComplex.isRelLowerSet_faces _ (adjoin q).property).2
        (Finset.filter_subset _ _) ?_⟩, fun _ _ h =>
      Finset.filter_subset_filter _ (adjoin.monotone h)⟩
    by_cases hq : q.val.val ∈ subdivision K A
    · have hkeep := old_keep q hq
      have he : (adjoin q).val = q.val.val := by
        dsimp only [adjoin, OrderHom.coe_mk]
        rw [dite_eq_left hq]
      rw [he, Finset.filter_true_of_mem hkeep.2.2]
      exact hkeep.1
    · have he : (adjoin q).val = insert t q.val.val := by
        dsimp only [adjoin, OrderHom.coe_mk]
        rw [dite_eq_right hq]
      exact ⟨t, Finset.mem_filter.mpr ⟨he ▸ Finset.mem_insert_self _ _, ht⟩⟩
  have hup (q : Allowed K p) : incOrder p q ≤ adjoin q := by
    change q.val ≤ (if hq : q.val.val ∈ subdivision K A then q.val else
      ⟨insert t q.val.val, insert_mem q hq⟩)
    by_cases hq : q.val.val ∈ subdivision K A
    · rw [dite_eq_left hq]
    · rw [dite_eq_right hq]
      exact Finset.subset_insert _ _
  have hc := (collar_chain_symm
    (descending_collar_maps p adjoin (incOrder p) hup)).trans
      (descending_collar_maps p adjoin trim (fun _ => Finset.filter_subset _ _))
  exact categorical_of_flag_factor hPK hcat trim (fun q => ⟨(trim q).property.1,
    (trim q).property.2.1, fun a ha => (Finset.mem_filter.mp ha).2⟩) hc

private theorem in_old_of_all (q : Face (sd K)) :
    q.val ∈ subdivision K A ↔ ∀ a ∈ q.val, a.val ∈ A :=
  ⟨fun h => h.2.2, fun h => ⟨q.property.1, q.property.2.1, h⟩⟩

private theorem new_below_simplex (hK : K = A ⊔ simplex σ) {a : Face K}
    (ha : a.val ∉ A) : a.val ∈ simplex σ :=
  (mem_union_cases hK a.property).resolve_left ha

private theorem facet_le_old (hOld : ∀ s ∈ simplex σ, s ∈ A ↔ ¬ J ⊆ s)
    {j : V} (hj : j ∈ J) : simplex (σ.erase j) ≤ A := by
  intro s hs
  exact (hOld s ⟨hs.1, hs.2.trans (Finset.erase_subset _ _)⟩).mpr
    (fun h => (Finset.notMem_erase j σ) (hs.2 (h hj)))

private theorem facet_in_piece (hOld : ∀ s ∈ simplex σ, s ∈ A ↔ ¬ J ⊆ s)
    (cover : ∀ s ∈ A, s ∈ P₀ ∨ s ∈ P₁) {j : V} (hj : j ∈ J)
    (h₁ : ¬ simplex (σ.erase j) ≤ P₁) : simplex (σ.erase j) ≤ P₀ := by
  by_cases hne : (σ.erase j).Nonempty
  · have htop : σ.erase j ∈ A := facet_le_old hOld hj ⟨hne, Finset.Subset.rfl⟩
    rcases cover _ htop with h | h
    · exact fun _ hs => (P₀.isRelLowerSet_faces h).2 hs.2 hs.1
    · exact (h₁ (fun _ hs => (P₁.isRelLowerSet_faces h).2 hs.2 hs.1)).elim
  · exact fun _ hs => (hne (hs.1.mono hs.2)).elim

private theorem new_flag_in_simplex {q : Face (sd K)} (hK : K = A ⊔ simplex σ)
    (hq : q.val ∉ subdivision K A) :
    ∀ a ∈ q.val, a.val ∈ simplex σ := by
  have hn : ∃ b ∈ q.val, b.val ∉ A := by
    by_contra h
    exact hq ((in_old_of_all q).mpr (fun b hb => by
      by_contra hba
      exact h ⟨b, hb, hba⟩))
  obtain ⟨b, hb, hbA⟩ := hn
  have hbσ := new_below_simplex hK hbA
  intro a ha
  by_cases haA : a.val ∈ A
  · have hab : a ≤ b := (flag_comparable q.property ha hb).resolve_right fun hba =>
      hbA ((A.isRelLowerSet_faces haA).2 hba (K.isRelLowerSet_faces b.property).1)
    exact ⟨(K.isRelLowerSet_faces a.property).1,
      (show a.val ⊆ b.val from hab).trans hbσ.2⟩
  · exact new_below_simplex hK haA

private theorem categorical_in_ambient (hAK : A ≤ K) (hPA : P ≤ A)
    (hcat : CategoricalIn hPA) : CategoricalIn (hPA.trans hAK) := by
  obtain ⟨c, hc⟩ := hcat
  exact ⟨includeSubcomplex hAK c, comp_chains id (includeSubcomplex hAK)
    id_simplicial (include_subcomplex_simplicial hAK) hc⟩

private structure Regions (K A : PreAbstractSimplicialComplex V)
    (P : Bool → PreAbstractSimplicialComplex V) where
  piece : Bool → PreAbstractSimplicialComplex (Face (sd K))
  full : ∀ i, FullIn (piece i) (sd (sd K))
  exact_old : ∀ i, piece i ⊓ D2 K A = D2 K (P i)
  covers_vertices : ∀ q : Vertex (sd (sd K)), ∃ i, {q.val} ∈ piece i
  categorical : ∀ i, CategoricalIn (full i).1

private theorem mixed_regions [Finite V]
    (P : Bool → PreAbstractSimplicialComplex V) (hK : K = A ⊔ simplex σ)
    (hJ : J ⊆ σ) (hOld : ∀ s ∈ simplex σ, s ∈ A ↔ ¬ J ⊆ s)
    (hPA : ∀ i, P i ≤ A) (hcover : ∀ s ∈ A, s ∈ P false ∨ s ∈ P true)
    (hcat : ∀ i, CategoricalIn (hPA i))
    (hyes : ∃ j ∈ J, simplex (σ.erase j) ≤ P true)
    (hno : ∃ j ∈ J, ¬ simplex (σ.erase j) ≤ P true) :
    Nonempty (Regions K A P) := by
  have hAK : A ≤ K := by rw [hK]; exact le_sup_left
  let τ := J.filter fun j => simplex (σ.erase j) ≤ P true
  have hτne : τ.Nonempty := by
    obtain ⟨j, hj, hj₁⟩ := hyes
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, hj₁⟩⟩
  have hτ : τ ∈ P false := by
    obtain ⟨j, hj, hj₁⟩ := hno
    apply facet_in_piece hOld hcover hj hj₁
    refine ⟨hτne, Finset.subset_erase.mpr ⟨?_, ?_⟩⟩
    · exact (Finset.filter_subset _ _).trans hJ
    · exact fun h => hj₁ (Finset.mem_filter.mp h).2
  let t : Face K := ⟨τ, hAK (hPA false hτ)⟩
  let p (i : Bool) : Face (sd K) → Bool := match i with
    | false => fun q => decide (anchored A (P false) t q)
    | true => fun q => decide (oldOrMeeting A (P true) q)
  have old (i : Bool) (q : Face (sd K)) (hq : q.val ∈ subdivision K A) :
      p i q = true ↔ q.val ∈ subdivision K (P i) := by
    cases i
    · simp only [p, decide_eq_true_eq, anchored, ite_eq_left hq]
    · simp only [p, decide_eq_true_eq, oldOrMeeting, ite_eq_left hq]
  have cats (i : Bool) : CategoricalIn (region_full (p i)).1 := by
    cases i
    · exact anchored_categorical ((hPA false).trans hAK)
        (categorical_in_ambient hAK (hPA false) (hcat false)) t hτ
    · exact oldOrMeeting_categorical ((hPA true).trans hAK)
        (categorical_in_ambient hAK (hPA true) (hcat true))
  refine ⟨⟨fun i => FlagRegion K (p i), fun i => region_full (p i),
    fun i => region_restrict (hPA i) (old i), ?_, cats⟩⟩
  intro v
  let q := v.val
  by_cases hq : q.val ∈ subdivision K A
  · obtain ⟨a, ha, htop⟩ := flag_top (show q.val ∈ sd K from q.property)
    rcases hcover _ (hq.2.2 a ha) with h | h
    · exact ⟨false, region_vertex.mpr ((old false q hq).mpr (flag_subdivision_of_top
        q.property htop h))⟩
    · exact ⟨true, region_vertex.mpr ((old true q hq).mpr (flag_subdivision_of_top
        q.property htop h))⟩
  · by_cases hmeet : ∃ a ∈ q.val, a.val ∈ P true
    · refine ⟨true, region_vertex.mpr (decide_eq_true (show oldOrMeeting A (P true) q from ?_))⟩
      simpa only [oldOrMeeting, ite_eq_right hq] using hmeet
    · refine ⟨false, region_vertex.mpr (decide_eq_true (show anchored A (P false) t q from ?_))⟩
      rw [anchored, ite_eq_right hq]
      have hσ := new_flag_in_simplex hK hq
      intro a ha
      have ha₁ : a.val ∉ P true := fun h => hmeet ⟨a, ha, h⟩
      refine ⟨?_, fun haA => (hcover _ haA).resolve_right ha₁⟩
      change τ ⊆ a.val
      intro j hj
      by_contra hj'
      have hf := (Finset.mem_filter.mp hj).2
      exact ha₁ (hf ⟨(hσ a ha).1, Finset.subset_erase.mpr ⟨(hσ a ha).2, hj'⟩⟩)

private theorem sd_connected
    (h : ∀ u v : Vertex K, (skeleton K).Reachable u v) :
    ∀ u v : Vertex (sd K), (skeleton (sd K)).Reachable u v := by
  intro u v
  obtain ⟨a, ha⟩ := (K.isRelLowerSet_faces u.val.property).1
  obtain ⟨b, hb⟩ := (K.isRelLowerSet_faces v.val.property).1
  let x : Vertex K := ⟨a, (K.isRelLowerSet_faces u.val.property).2
    (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty _)⟩
  let y : Vertex K := ⟨b, (K.isRelLowerSet_faces v.val.property).2
    (Finset.singleton_subset_iff.mpr hb) (Finset.singleton_nonempty _)⟩
  obtain ⟨p⟩ := h x y
  obtain ⟨px, _⟩ := incident_face_walk (le_refl K) u.val x ha
  obtain ⟨py, _⟩ := incident_face_walk (le_refl K) v.val y hb
  obtain ⟨pq, _⟩ := bisect_walk (le_refl K) p
  exact ⟨px.reverse.append (pq.append py)⟩

private def pureNew (A : PreAbstractSimplicialComplex V) (q : Face (sd K)) : Prop :=
  ∀ a ∈ q.val, a.val ∉ A

private theorem old_pureNew_incomparable {q r : Face (sd K)}
    (hq : q.val ∈ subdivision K A) (hr : pureNew A r) (h : q ≤ r ∨ r ≤ q) : False := by
  rcases h with h | h
  · obtain ⟨a, ha⟩ := q.property.1
    exact hr a (h ha) (hq.2.2 a ha)
  · obtain ⟨a, ha⟩ := r.property.1
    exact hr a ha (hq.2.2 a (h ha))

private def singletonFlag (top : Face K) : Face (sd K) :=
  ⟨{top}, (vertexOfFace K top).property⟩

private theorem pureNew_collapse [Finite V] (hK : K = A ⊔ simplex σ)
    (top : Face K) (htop : top.val = σ) :
    ReflTransGen Contiguous
      (includeSubcomplex (region_full (K := K) (fun q => decide (pureNew A q))).1)
      (fun _ => vertexOfFace (sd K) (singletonFlag top)) := by
  let p (q : Face (sd K)) := decide (pureNew A q)
  let adjoin : Allowed K p →o Face (sd K) :=
    ⟨fun q => ⟨insert top q.val.val, flag_insert q.val top (fun a ha => Or.inr (by
      have hq : pureNew A q.val := of_decide_eq_true q.property
      change a.val ⊆ top.val
      rw [htop]
      exact (new_below_simplex hK (hq a ha)).2))⟩, by
        intro q r h a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (h ha)⟩
  let tip : Allowed K p →o Face (sd K) :=
    ⟨fun _ => singletonFlag top, fun _ _ _ => le_rfl⟩
  have h₁ := descending_collar_maps p adjoin (incOrder p)
    (fun q => Finset.subset_insert top q.val.val)
  have h₂ := descending_collar_maps p adjoin tip
    (fun _ => Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
  rw [incOrder_map] at h₁
  exact (collar_chain_symm h₁).trans h₂

private theorem oldOrPureNew_categorical [Finite V] (hPK : P ≤ K) (hPA : P ≤ A)
    (hcat : CategoricalIn hPK)
    (hK : K = A ⊔ simplex σ) (hσ : σ.Nonempty)
    (connected : ∀ u v : Vertex (sd (sd K)), (skeleton (sd (sd K))).Reachable u v) :
    CategoricalIn (region_full (fun q => decide
      (q.val ∈ subdivision K P ∨ pureNew A q))).1 := by
  let p (q : Face (sd K)) := decide (q.val ∈ subdivision K P ∨ pureNew A q)
  let R := FlagRegion K p
  let label (q : Face (sd K)) := decide (q.val ∈ subdivision K A)
  have split {s : Finset (Face (sd K))} (hs : s ∈ R) {q : Face (sd K)} (hq : q ∈ s) :
      q.val ∈ subdivision K P ∨ pureNew A q := of_decide_eq_true (hs.2 q hq)
  have old {q : Face (sd K)} (hq : q.val ∈ subdivision K P) :
      q.val ∈ subdivision K A := subdivision_mono K hPA hq
  have uniform (s : Finset (Face (sd K))) (hs : s ∈ R) :
      ∃ i, ∀ q ∈ s, label q = i := by
    obtain ⟨q, hq⟩ := hs.1.1
    rcases split hs hq with hqP | hqN
    · refine ⟨true, fun r hr => ?_⟩
      rcases split hs hr with hrP | hrN
      · exact decide_eq_true (old hrP)
      · exact (old_pureNew_incomparable (old hqP) hrN (flag_comparable hs.1 hq hr)).elim
    · refine ⟨false, fun r hr => ?_⟩
      apply decide_eq_false
      intro hrA
      exact old_pureNew_incomparable hrA hqN (flag_comparable hs.1 hr hq)
  let part (i : Bool) := colourPiece (P := R) label i
  have part_le (i : Bool) : part i ≤ sd (sd K) := fun _ hs => hs.1.1
  have old_le : part true ≤ D2 K P := by
    intro s hs
    refine ⟨hs.1.1.1, hs.1.1.2.1, fun q hq => ?_⟩
    have he : label q = true := of_decide_eq_true (hs.2 q hq)
    have hqA : q.val ∈ subdivision K A := of_decide_eq_true he
    exact (split hs.1 hq).resolve_right
      (fun hn => old_pureNew_incomparable hqA hn (Or.inl le_rfl))
  let n (q : Face (sd K)) := decide (pureNew A q)
  have new_le : part false ≤ FlagRegion K n := by
    intro s hs
    refine ⟨hs.1.1, fun q hq => decide_eq_true ?_⟩
    have he : label q = false := of_decide_eq_true (hs.2 q hq)
    exact (split hs.1 hq).resolve_left (fun hP => (of_decide_eq_false he) (old hP))
  have top_mem : σ ∈ K := by
    rw [hK]
    exact Or.inr (show σ ∈ simplex σ from ⟨hσ, Finset.Subset.rfl⟩)
  let top : Face K := ⟨σ, top_mem⟩
  obtain ⟨c, hc⟩ := categorical_of_subdivision_le old_le (subdivision_full K P).1
    (categorical_of_subdivision_le (le_refl (subdivision K P)) hPK hcat)
  let starts (i : Bool) : Vertex (part i) → Vertex (sd (sd K)) :=
    includeSubcomplex (part_le i)
  let ends (i : Bool) : Vertex (part i) → Vertex (sd (sd K)) := fun _ => c
  have branch (i : Bool) : ReflTransGen Contiguous (starts i) (ends i) := by
    cases i
    · have hnew := comp_chains (includeSubcomplex new_le) id
        (include_subcomplex_simplicial new_le) id_simplicial (pureNew_collapse hK top rfl)
      exact hnew.trans (constant_chain_of_reachable (connected _ c))
    · exact hc
  have hstart (i : Bool) : Contiguous (starts i) (starts i) := by
    intro s hs
    rw [Finset.union_idempotent]
    exact include_subcomplex_simplicial (part_le i) s hs
  have hend (i : Bool) : Contiguous (ends i) (ends i) := by
    intro s hs
    rw [Finset.union_idempotent]
    exact constant_simplicial c s hs
  exact ⟨c, glue_contiguity label uniform starts ends hstart hend branch⟩

private theorem monochromatic_regions [Finite V]
    (P : Bool → PreAbstractSimplicialComplex V) (hK : K = A ⊔ simplex σ)
    (hσ : σ.Nonempty) (hOld : ∀ s ∈ simplex σ, s ∈ A ↔ ¬ J ⊆ s)
    (hPA : ∀ i, P i ≤ A) (hcover : ∀ s ∈ A, s ∈ P false ∨ s ∈ P true)
    (hcat : ∀ i, CategoricalIn (hPA i)) (k : Bool)
    (mono : ∀ j ∈ J, simplex (σ.erase j) ≤ P k)
    (connected : ∀ u v : Vertex K, (skeleton K).Reachable u v) :
    Nonempty (Regions K A P) := by
  have hAK : A ≤ K := by rw [hK]; exact le_sup_left
  let p (i : Bool) (q : Face (sd K)) : Bool :=
    if i = k then decide (oldOrMeeting A (P i) q)
    else decide (q.val ∈ subdivision K (P i) ∨ pureNew A q)
  have old (i : Bool) (q : Face (sd K)) (hq : q.val ∈ subdivision K A) :
      p i q = true ↔ q.val ∈ subdivision K (P i) := by
    by_cases hi : i = k
    · simp only [p, ite_eq_left hi, decide_eq_true_eq, oldOrMeeting, ite_eq_left hq]
    · have hn : ¬ pureNew A q := fun h =>
        old_pureNew_incomparable hq h (Or.inl le_rfl)
      simp only [p, ite_eq_right hi, decide_eq_true_eq, hn, or_false]
  have cats (i : Bool) : CategoricalIn (region_full (p i)).1 := by
    have hi := categorical_in_ambient hAK (hPA i) (hcat i)
    by_cases hik : i = k
    · simpa only [p, ite_eq_left hik] using oldOrMeeting_categorical (A := A) _ hi
    · simpa only [p, ite_eq_right hik] using
        oldOrPureNew_categorical _ (hPA i) hi hK hσ (sd_connected (sd_connected connected))
  refine ⟨⟨fun i => FlagRegion K (p i), fun i => region_full (p i),
    fun i => region_restrict (hPA i) (old i), ?_, cats⟩⟩
  intro v
  let q := v.val
  by_cases hq : q.val ∈ subdivision K A
  · obtain ⟨a, ha, htop⟩ := flag_top (show q.val ∈ sd K from q.property)
    rcases hcover _ (hq.2.2 a ha) with h | h
    · exact ⟨false, region_vertex.mpr ((old false q hq).mpr
        (flag_subdivision_of_top q.property htop h))⟩
    · exact ⟨true, region_vertex.mpr ((old true q hq).mpr
        (flag_subdivision_of_top q.property htop h))⟩
  · by_cases hn : ∃ a ∈ q.val, a.val ∈ A
    · obtain ⟨a, ha, haA⟩ := hn
      have haσ := new_flag_in_simplex hK hq a ha
      obtain ⟨j, hj, hja⟩ := Finset.not_subset.mp ((hOld a.val haσ).mp haA)
      have haP := mono j hj (show a.val ∈ simplex (σ.erase j) from
        ⟨haσ.1, Finset.subset_erase.mpr ⟨haσ.2, hja⟩⟩)
      refine ⟨k, region_vertex.mpr ?_⟩
      have hm : oldOrMeeting A (P k) q := by
        rw [oldOrMeeting, ite_eq_right hq]
        exact ⟨a, ha, haP⟩
      simpa only [p, ite_eq_left rfl] using (decide_eq_true hm)
    · have hp : pureNew A q := fun a ha haA => hn ⟨a, ha, haA⟩
      have hk : (!k) ≠ k := by cases k <;> simp
      refine ⟨!k, region_vertex.mpr ?_⟩
      simp only [p, ite_eq_right hk, decide_eq_true_eq]
      exact Or.inr hp

/-- Exact restrictions at the third ordinary subdivision in the common ambient. -/
def HasExactTwoCoverAtDepthThree (K A : PreAbstractSimplicialComplex V)
    (P : Bool → PreAbstractSimplicialComplex V) : Prop :=
  ∃ Y : Bool → PreAbstractSimplicialComplex (Face (sd (sd K))),
    ∃ hY : ∀ i, FullIn (Y i) (sd (sd (sd K))),
      (∀ s ∈ sd (sd (sd K)), ∃ i, s ∈ Y i) ∧
      (∀ i, Y i ⊓ iteratedSubcomplex K A 3 = iteratedSubcomplex K (P i) 3) ∧
      ∀ i, CategoricalIn (hY i).1

/-- The two exact restrictions identify the common old overlap as well. -/
theorem exact_old_overlap
    {Y : Bool → PreAbstractSimplicialComplex (Face (sd (sd K)))}
    (P : Bool → PreAbstractSimplicialComplex V)
    (hY : ∀ i, Y i ⊓ iteratedSubcomplex K A 3 = iteratedSubcomplex K (P i) 3) :
    (Y false ⊓ Y true) ⊓ iteratedSubcomplex K A 3 =
      iteratedSubcomplex K (P false ⊓ P true) 3 := by
  have hmeet :
      (Y false ⊓ Y true) ⊓ iteratedSubcomplex K A 3 =
        (Y false ⊓ iteratedSubcomplex K A 3) ⊓ (Y true ⊓ iteratedSubcomplex K A 3) := by
    apply le_antisymm
    · intro s hs
      exact ⟨⟨hs.1.1, hs.2⟩, ⟨hs.1.2, hs.2⟩⟩
    · intro s hs
      exact ⟨⟨hs.1.1, hs.2.1⟩, hs.1.2⟩
  rw [hmeet, hY false, hY true]
  have hamb (B : PreAbstractSimplicialComplex V) :
      iteratedSubcomplex K B 3 ≤ (iteratedAmbient K 3).2 :=
    (subdivision_full (sd (sd K)) (iteratedSubcomplex K B 2)).1
  apply le_antisymm
  · intro s hs
    have hsK := hamb (P false) hs.1
    apply (mem_iteratedSubcomplex_iff 3 hsK).mpr
    change originalSupport K 3 s ∈ P false ∧ originalSupport K 3 s ∈ P true
    exact ⟨(mem_iteratedSubcomplex_iff 3 hsK).mp hs.1,
      (mem_iteratedSubcomplex_iff 3 hsK).mp hs.2⟩
  · intro s hs
    have hsK := hamb (P false ⊓ P true) hs
    have hp := (mem_iteratedSubcomplex_iff 3 hsK).mp hs
    change originalSupport K 3 s ∈ P false ∧ originalSupport K 3 s ∈ P true at hp
    exact ⟨(mem_iteratedSubcomplex_iff 3 hsK).mpr hp.1,
      (mem_iteratedSubcomplex_iff 3 hsK).mpr hp.2⟩

private theorem depth_three_of_regions [Finite V]
    {P : Bool → PreAbstractSimplicialComplex V} (R : Regions K A P)
    (hPA : ∀ i, P i ≤ A) (hcover : A = P false ⊔ P true) :
    HasExactTwoCoverAtDepthThree K A P := by
  have hcontain (i : Bool) : D2 K (P i) ≤ R.piece i := by
    rw [← R.exact_old i]
    exact inf_le_left
  let _ : Finite (iteratedAmbient K 2).fst := inferInstanceAs (Finite (Face (sd K)))
  refine exact_extension_of_vertex_cover (T := D2 K A) (fun i => D2 K (P i)) R.piece
    (fun i => d2_le K (hPA i)) hcontain R.full ?_ R.covers_vertices R.categorical
  intro s hs
  change s ∈ iteratedSubcomplex K A 2 at hs
  rw [hcover] at hs
  change s ∈ D2 K (P false ⊔ P true) at hs
  have hsplit : D2 K (P false ⊔ P true) = D2 K (P false) ⊔ D2 K (P true) :=
    d2_sup K _ _
  rw [hsplit] at hs
  rcases (show s ∈ D2 K (P false) ∨ s ∈ D2 K (P true) from hs) with hf | ht
  · exact ⟨false, hf⟩
  · exact ⟨true, ht⟩

/-- A mixed attachment transports the prescribed cover to depth three in
every edge component. The missing-label face may also belong to the second
piece. -/
theorem exact_extension_mixed_shelling [Finite V]
    (P : Bool → PreAbstractSimplicialComplex V) (hK : K = A ⊔ simplex σ)
    (hJ : J ⊆ σ) (hOld : ∀ s ∈ simplex σ, s ∈ A ↔ ¬ J ⊆ s)
    (hcover : A = P false ⊔ P true)
    (hPA : ∀ i, P i ≤ A) (hcat : ∀ i, CategoricalIn (hPA i))
    (hyes : ∃ j ∈ J, simplex (σ.erase j) ≤ P true)
    (hno : ∃ j ∈ J, ¬ simplex (σ.erase j) ≤ P true) :
    HasExactTwoCoverAtDepthThree K A P := by
  have cover : ∀ s ∈ A, s ∈ P false ∨ s ∈ P true := by
    intro s hs
    rw [hcover] at hs
    exact hs
  obtain ⟨R⟩ := mixed_regions P hK hJ hOld hPA cover hcat hyes hno
  exact depth_three_of_regions R hPA hcover

/-- A depth-zero categorical two-cover extends across a single shelling
simplex attachment at the common depth three. An ambient edge path is used
in the monochromatic case to join the two component constants. -/
theorem exact_extension_shelling [Finite V]
    (P : Bool → PreAbstractSimplicialComplex V) (hK : K = A ⊔ simplex σ)
    (hJ : J ⊆ σ) (hJne : J.Nonempty)
    (hOld : ∀ s ∈ simplex σ, s ∈ A ↔ ¬ J ⊆ s)
    (hcover : A = P false ⊔ P true)
    (hPA : ∀ i, P i ≤ A) (hcat : ∀ i, CategoricalIn (hPA i))
    (connected : (∃ i, ∀ j ∈ J, simplex (σ.erase j) ≤ P i) →
      ∀ u v : Vertex K, (skeleton K).Reachable u v) :
    HasExactTwoCoverAtDepthThree K A P := by
  have cover : ∀ s ∈ A, s ∈ P false ∨ s ∈ P true := by
    intro s hs
    rw [hcover] at hs
    exact hs
  by_cases mono : ∃ i, ∀ j ∈ J, simplex (σ.erase j) ≤ P i
  · have hc := connected mono
    obtain ⟨i, hi⟩ := mono
    obtain ⟨R⟩ := monochromatic_regions P hK (hJne.mono hJ) hOld hPA cover hcat i hi hc
    exact depth_three_of_regions R hPA hcover
  · have hyes : ∃ j ∈ J, simplex (σ.erase j) ≤ P true := by
      by_contra h
      apply mono
      refine ⟨false, fun j hj => facet_in_piece hOld cover hj ?_⟩
      exact fun he => h ⟨j, hj, he⟩
    have hno : ∃ j ∈ J, ¬ simplex (σ.erase j) ≤ P true := by
      by_contra h
      apply mono
      refine ⟨true, fun j hj => ?_⟩
      by_contra he
      exact h ⟨j, hj, he⟩
    exact exact_extension_mixed_shelling P hK hJ hOld hcover hPA hcat hyes hno

/-- The elementary expansion is the shelling step with missing labels the
vertices of the free face. -/
theorem exact_extension_elementary_expansion [Fintype V] [DecidableEq V]
    (E : CollapsePair V) (P : Bool → PreAbstractSimplicialComplex V)
    (hcover : E.retained = P false ⊔ P true)
    (hPA : ∀ i, P i ≤ E.retained) (hcat : ∀ i, CategoricalIn (hPA i))
    (connected : ∀ u v : Vertex E.ambient, (skeleton E.ambient).Reachable u v) :
    HasExactTwoCoverAtDepthThree E.ambient E.retained P := by
  have hK : E.ambient = E.retained ⊔ simplex E.upper := by
    refine le_antisymm ?_ (sup_le E.retained_le (fun s hs =>
      (E.ambient.isRelLowerSet_faces E.upper_mem).2 hs.2 hs.1))
    intro s hs
    by_cases h : E.lower ⊆ s
    · refine Or.inr ⟨(E.ambient.isRelLowerSet_faces hs).1, ?_⟩
      by_cases he : s = E.lower
      · rw [he]
        exact Finset.subset_insert _ _
      · rw [E.free s hs (Finset.ssubset_iff_subset_ne.mpr ⟨h, Ne.symm he⟩)]
    · exact Or.inl ⟨hs, h⟩
  apply exact_extension_shelling P hK (Finset.subset_insert _ _) E.lower_nonempty
    ?_ hcover hPA hcat (fun _ => connected)
  intro s hs
  exact ⟨fun h => h.2, fun h => ⟨
    (E.ambient.isRelLowerSet_faces E.upper_mem).2 hs.2 hs.1, h⟩⟩

end
end D5.S3.Topology.StableCategory.ShellingExactExtension
