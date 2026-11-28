/- GID: D5/S3/Topology/StableCategory/InducedCategoricalCover
   generality: G
   mirror-B: none(waiver:support-for-the-tetrahedral-categorical-cover)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contracting induced colour regions gives a categorical lower cover. -/

import D5.S3.Topology.OrdinaryCollarRetraction
import D5.S3.Topology.StableCategory.OrdinaryContiguityLift
import D5.S3.Topology.SubdivisionCategoricalCover
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.WellFounded

/-! A categorical cover from contiguity contractions of induced subcomplexes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.InducedCategoricalCover

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous faceImage)
open ConnectedCategoryGraft (Categorical HasCategoricalCover)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryContiguityLift (Simplicial face_map_fence includeSubcomplex
  include_subcomplex_simplicial)
open PartialOrder (NonemptyFiniteChains)
open Relation (ReflTransGen)
open private faceMap from D5.S3.Topology.StableCategory.OrdinaryContiguityLift
open private categorical_of_meeting map_fence from D5.S3.Topology.SubdivisionCategoricalCover
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X
attribute [local instance] Classical.propDecidable

variable {X : Type} {K : PreAbstractSimplicialComplex X}

private def meeting (p : X → Bool) : Set (Face K) :=
  {s | ∃ x ∈ s.val, p x = true}

private def cut (p : X → Bool) : meeting (K := K) p →o Face (colourComplex K p) where
  toFun s := by
    let t := s.val.val.filter (p · = true)
    have ht : t.Nonempty := by
      obtain ⟨x, hx, hp⟩ := s.property
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, hp⟩⟩
    exact ⟨t, ⟨(K.isRelLowerSet_faces s.val.property).2 (Finset.filter_subset _ _) ht,
      fun _ hy => (Finset.mem_filter.mp hy).2⟩⟩
  monotone' _ _ h := Finset.filter_subset_filter _ h

private theorem categorical_meeting (p : X → Bool) (b : Vertex K)
    (h : ReflTransGen Contiguous
      (includeSubcomplex (show colourComplex K p ≤ K from fun _ hs => hs.1)) (fun _ => b)) :
    Categorical (meeting (K := K) p) := by
  let A := colourComplex K p
  have hle : A ≤ K := fun _ hs => hs.1
  let inc := includeSubcomplex hle
  let r := cut (K := K) p
  let i : meeting (K := K) p →o Face K := (OrderEmbedding.subtype _).toOrderHom
  have hconst : Simplicial (fun _ : Vertex A => b) := by
    intro s hs
    simpa only [faceImage, Finset.image_const (A.isRelLowerSet_faces hs).1.attach]
      using b.property
  let fi := faceMap inc (include_subcomplex_simplicial hle)
  let fc := faceMap (fun _ : Vertex A => b) hconst
  have hstart : fi.comp r ≤ i := by
    intro s y hy
    obtain ⟨v, hv, rfl⟩ := (mem_faceImage_iff inc (r s).property y).mp hy
    change v.val ∈ s.val.val
    change v.val ∈ s.val.val.filter (p · = true) at hv
    exact (Finset.filter_subset _ _) hv
  have hend : fc.comp r = OrderHom.const _ (⟨{b.val}, b.property⟩ : Face K) := by
    apply OrderHom.ext
    funext s
    apply Subtype.ext
    exact Finset.image_const (A.isRelLowerSet_faces (r s).property).1.attach _
  have hf : Relation.EqvGen (· ≤ ·) (fi.comp r) (fc.comp r) :=
    map_fence (fun f : Face A →o Face K => f.comp r)
      (fun _ _ hfg => .rel _ _ (fun s => (OrderHom.le_def.mp hfg) (r s)))
      (face_map_fence (include_subcomplex_simplicial hle) hconst h)
  rw [hend] at hf
  exact ⟨_, .trans _ _ _ (.symm _ _ (.rel _ _ hstart)) hf⟩

private def flags (p : X → Bool) : Set (NonemptyFiniteChains (Face K)) :=
  {s | ∀ a ∈ s.finset, a ∈ meeting (K := K) p}

/-- A partition into induced subcomplexes that contract by contiguity in the
ambient complex gives a categorical lower cover of the subdivided face poset.
A flag belongs to any colour meeting its least face. -/
theorem has_categorical_cover_of_partition [Finite X] {n : ℕ} (label : X → Fin n)
    (contract : ∀ j : Fin n, ∃ b : Vertex K,
      ReflTransGen Contiguous
        (includeSubcomplex (show colourComplex K (fun x => decide (label x = j)) ≤ K
          from fun _ hs => hs.1)) (fun _ => b)) :
    HasCategoricalCover (NonemptyFiniteChains (Face K)) n := by
  let p (j : Fin n) (x : X) := decide (label x = j)
  refine ⟨fun j => flags (K := K) (p j), ?_, ?_⟩
  · intro j
    refine ⟨fun _ _ hab hs a ha => hs a (hab ha), ?_⟩
    obtain ⟨b, hb⟩ := contract j
    apply categorical_of_meeting (categorical_meeting (p j) b hb)
    intro s
    obtain ⟨a, ha⟩ := s.val.nonempty
    exact ⟨a, ha, s.property a ha⟩
  · intro s
    obtain ⟨a, ha⟩ := s.nonempty
    obtain ⟨m, _, hm⟩ := Finite.exists_le_minimal (p := fun f : Face K => f ∈ s.finset) ha
    have hleast (f : Face K) (hf : f ∈ s.finset) : m ≤ f :=
      (s.comparable ⟨m, hm.1⟩ ⟨f, hf⟩).elim id (hm.2 hf)
    obtain ⟨x, hx⟩ := (K.isRelLowerSet_faces m.property).1
    exact ⟨label x, fun f hf => ⟨x, hleast f hf hx, decide_eq_true rfl⟩⟩

end

end D5.S3.Topology.StableCategory.InducedCategoricalCover
