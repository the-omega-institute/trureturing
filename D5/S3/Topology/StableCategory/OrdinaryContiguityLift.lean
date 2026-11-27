/- GID: D5/S3/Topology/StableCategory/OrdinaryContiguityLift
   generality: G
   mirror-B: none(waiver:support-for-the-tetrahedral-refinement)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contiguity persists under ordinary simplicial subdivision. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.DescendingClosureContiguity
import D5.S3.Topology.GraphSubdivisionIntervals
import D5.S3.Topology.OrdinarySubdivisionMap

/-! Contiguity of simplicial maps persists under ordinary subdivision. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.OrdinaryContiguityLift

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous faceImage sd skeleton vertexOfFace)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open DescendingClosureContiguity (exists_relative_contiguity_of_le)
open OrdinarySubdivisionMap (iterate)
open Relation (ReflTransGen)
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals
open private image from D5.S3.Topology.OrdinarySubdivisionMap

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

variable {X Y : Type} {K : PreAbstractSimplicialComplex X} {L : PreAbstractSimplicialComplex Y}

/-- A vertex map is simplicial when it sends each nonempty face to a face. -/
def Simplicial (f : Vertex K → Vertex L) : Prop :=
  ∀ s (hs : s ∈ K), faceImage f hs ∈ L

def ofTotal (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L) :
    Vertex K → Vertex L :=
  fun v => ⟨f v.val, by simpa only [image, Finset.image_singleton] using hf _ v.property⟩

private theorem ofTotal_faceImage (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L)
    (s : Finset X) (hs : s ∈ K) :
    faceImage (ofTotal f hf) hs = image s f := by
  ext y
  rw [mem_faceImage_iff, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x.val, hx, h⟩
  · rintro ⟨x, hx, h⟩
    have hvertex : ({x} : Finset X) ∈ K := (K.isRelLowerSet_faces hs).2
      (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty _)
    exact ⟨⟨x, hvertex⟩, hx, h⟩

theorem of_total_simplicial (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L) :
    Simplicial (ofTotal f hf) := by
  intro s hs
  rw [ofTotal_faceImage]
  exact hf s hs

def includeSubcomplex {A B : PreAbstractSimplicialComplex X} (hle : A ≤ B) :
    Vertex A → Vertex B :=
  fun x => ⟨x.val, hle x.property⟩

theorem include_subcomplex_simplicial {A B : PreAbstractSimplicialComplex X} (hle : A ≤ B) :
    Simplicial (includeSubcomplex hle) := by
  intro s hs
  have h : faceImage (includeSubcomplex hle) hs = s := by
    ext x
    change x ∈ s.attach.image Subtype.val ↔ _
    rw [Finset.attach_image_val]
  rw [h]
  exact hle hs

/-- Face images compose, including for vertex maps identifying vertices. -/
theorem comp_image {Z : Type} {M : PreAbstractSimplicialComplex Z}
    (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L)
    (g : Y → Z) (hg : ∀ s ∈ L, image s g ∈ M) :
    ∀ s ∈ K, image s (g ∘ f) ∈ M := by
  intro s hs
  simpa only [← Finset.image_image] using hg (image s f) (hf s hs)

/-- Composition preserves the face-image condition for vertex maps. -/
theorem Simplicial.comp {Z : Type} {M : PreAbstractSimplicialComplex Z}
    {f : Vertex K → Vertex L} {g : Vertex L → Vertex M}
    (hg : Simplicial g) (hf : Simplicial f) : Simplicial (g ∘ f) := by
  intro s hs
  have ht := hf s hs
  have hi : faceImage (g ∘ f) hs = faceImage g ht := by
    ext y
    rw [mem_faceImage_iff, mem_faceImage_iff]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨f u, (mem_faceImage_iff f hs _).2 ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨u, hu, he⟩ := (mem_faceImage_iff f hs _).1 hv
      exact ⟨u, hu, congrArg (fun x : Vertex L => (g x).val) (Subtype.ext he)⟩
  rw [hi]
  exact hg _ ht

/-- Ordinary subdivision commutes with composition of simplicial vertex maps. -/
theorem iterate_comp {Z : Type} {M : PreAbstractSimplicialComplex Z}
    (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L)
    (g : Y → Z) (hg : ∀ s ∈ L, image s g ∈ M) (m : ℕ) :
    (iterate (g ∘ f) (comp_image f hf g hg) m).val =
      (iterate g hg m).val ∘ (iterate f hf m).val := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext s
    apply Subtype.ext
    change image s.val (iterate (g ∘ f) (comp_image f hf g hg) m).val =
      image (image s.val (iterate f hf m).val) (iterate g hg m).val
    rw [ih]
    exact Finset.image_image.symm

/-- Subdividing first by `a` steps and then by `b` steps gives the same
dependent pair of vertex type and complex as subdividing by `a + b`. -/
theorem iterated_ambient_add (K : PreAbstractSimplicialComplex X) (a b : ℕ) :
    iteratedAmbient (iteratedAmbient K a).2 b = iteratedAmbient K (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    exact congrArg (fun J : Σ V : Type, PreAbstractSimplicialComplex V =>
      (⟨Face J.2, sd J.2⟩ : Σ V : Type, PreAbstractSimplicialComplex V)) ih

private theorem constant_face_image (b : Vertex L) {s : Finset X} (hs : s ∈ K) :
    faceImage (fun _ : Vertex K => b) hs = {b.val} :=
  Finset.image_const (K.isRelLowerSet_faces hs).1.attach _

/-- In a single edge component of the target, all constant simplicial
maps are in the same contiguity class. -/
theorem constant_chain_of_reachable {a b : Vertex L} (h : (skeleton L).Reachable a b) :
    ReflTransGen Contiguous (fun _ : Vertex K => a) (fun _ : Vertex K => b) := by
  refine ReflTransGen.lift (fun v : Vertex L => fun _ : Vertex K => v) ?_ _ _
    ((SimpleGraph.reachable_iff_reflTransGen (G := skeleton L) a b).mp h)
  intro u v huv s hs
  rw [constant_face_image u hs, constant_face_image v hs]
  simpa only [Finset.singleton_union] using huv.2

theorem comp_chains {U V : Type}
    {P : PreAbstractSimplicialComplex U} {Q : PreAbstractSimplicialComplex V}
    (pre : Vertex P → Vertex K) (post : Vertex L → Vertex Q)
    (hpre : Simplicial pre) (hpost : Simplicial post)
    {f g : Vertex K → Vertex L} (h : ReflTransGen Contiguous f g) :
    ReflTransGen Contiguous (post ∘ f ∘ pre) (post ∘ g ∘ pre) := by
  refine ReflTransGen.lift (fun a => post ∘ a ∘ pre) ?_ _ _ h
  intro a b hab s hs
  let t := faceImage pre hs
  have ht : t ∈ K := hpre s hs
  let d := faceImage a ht ∪ faceImage b ht
  have hd : d ∈ L := hab t ht
  have hleft : faceImage (post ∘ a ∘ pre) hs ⊆ faceImage post hd := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff (post ∘ a ∘ pre) hs y).mp hy
    have hxt : (pre x).val ∈ t := (mem_faceImage_iff pre hs _).mpr ⟨x, hx, rfl⟩
    have hxd : (a (pre x)).val ∈ d := Finset.mem_union_left _
      ((mem_faceImage_iff a ht _).mpr ⟨pre x, hxt, rfl⟩)
    exact (mem_faceImage_iff post hd _).mpr ⟨a (pre x), hxd, rfl⟩
  have hright : faceImage (post ∘ b ∘ pre) hs ⊆ faceImage post hd := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff (post ∘ b ∘ pre) hs y).mp hy
    have hxt : (pre x).val ∈ t := (mem_faceImage_iff pre hs _).mpr ⟨x, hx, rfl⟩
    have hxd : (b (pre x)).val ∈ d := Finset.mem_union_right _
      ((mem_faceImage_iff b ht _).mpr ⟨pre x, hxt, rfl⟩)
    exact (mem_faceImage_iff post hd _).mpr ⟨b (pre x), hxd, rfl⟩
  have hne : (faceImage (post ∘ a ∘ pre) hs).Nonempty :=
    (P.isRelLowerSet_faces hs).1.attach.image _
  exact (Q.isRelLowerSet_faces (hpost d hd)).2 (Finset.union_subset hleft hright)
    (hne.mono Finset.subset_union_left)

private theorem image_mono (f : Vertex K → Vertex L) {s t : Finset X}
    (hs : s ∈ K) (ht : t ∈ K) (hst : s ⊆ t) : faceImage f hs ⊆ faceImage f ht := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff f hs y).mp hy
  exact (mem_faceImage_iff f ht _).mpr ⟨x, hst hx, rfl⟩

private def faceMap (f : Vertex K → Vertex L) (hf : Simplicial f) : Face K →o Face L where
  toFun s := ⟨faceImage f s.property, hf s.val s.property⟩
  monotone' := fun a b hab => image_mono f a.property b.property hab

private def onSubdivision (f : Face K →o Face L) : Vertex (sd K) → Vertex (sd L) :=
  fun u => vertexOfFace L (f u.val)

/-- The subdivided map sends a flag vertex to the image of its nonempty face. -/
def subdivide (f : Vertex K → Vertex L) (hf : Simplicial f) :
    Vertex (sd K) → Vertex (sd L) :=
  onSubdivision (faceMap f hf)

theorem subdivide_of_total (f : X → Y) (hf : ∀ s ∈ K, image s f ∈ L) :
    subdivide (ofTotal f hf) (of_total_simplicial f hf) =
      ofTotal (iterate f hf 1).val (iterate f hf 1).property := by
  funext v
  apply Subtype.ext
  apply Subtype.ext
  exact ofTotal_faceImage f hf v.val.val v.val.property

private theorem of_comparable [Finite X] (f g : Face K →o Face L) (hle : ∀ s, g s ≤ f s) :
    ReflTransGen Contiguous (onSubdivision f) (onSubdivision g) := by
  let _ := Fintype.ofFinite X
  let rank (s : Face K) := s.val.card
  have hrank : StrictMono rank := fun _ _ h => Finset.card_lt_card h
  have hbound (s : Face K) : rank s ≤ Fintype.card X := Finset.card_le_univ _
  obtain ⟨F, hfirst, hlast, _, _, hstep⟩ :=
    exists_relative_contiguity_of_le rank hrank f g hle _ hbound
  have adjacent (n : ℕ) : Contiguous (onSubdivision (F n)) (onSubdivision (F (n + 1))) := by
    intro s hs
    let a := onSubdivision (F n)
    let b := onSubdivision (F (n + 1))
    have hs' : IsChain (· ≤ ·) (s : Set (Face K)) := by
      intro p hp q hq hne
      exact (hs.2.1 hp hq hne).imp LT.lt.le LT.lt.le
    have hmem x (hx : x ∈ faceImage a hs ∪ faceImage b hs) :
        x ∈ F n '' (s : Set (Face K)) ∪ F (n + 1) '' (s : Set (Face K)) := by
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨v, hv, rfl⟩ := (mem_faceImage_iff a hs x).mp hx
        exact Or.inl ⟨v.val, hv, rfl⟩
      · obtain ⟨v, hv, rfl⟩ := (mem_faceImage_iff b hs x).mp hx
        exact Or.inr ⟨v.val, hv, rfl⟩
    have hne : (faceImage a hs).Nonempty := hs.1.attach.image _
    refine ⟨hne.mono Finset.subset_union_left, ?_, fun x _ => x.property⟩
    intro p hp q hq hpq
    exact (hstep n _ hs' (hmem _ hp) (hmem _ hq) hpq).imp
      (fun h => lt_of_le_of_ne h hpq) (fun h => lt_of_le_of_ne h hpq.symm)
  have reaches (n : ℕ) : ReflTransGen Contiguous (onSubdivision (F 0)) (onSubdivision (F n)) := by
    induction n with
    | zero => exact .refl
    | succ n ih => exact ih.tail (adjacent n)
  simpa only [hfirst, hlast] using reaches (Fintype.card X + 1)

private theorem reverse_chain {f g : Vertex (sd K) → Vertex (sd L)}
    (h : ReflTransGen Contiguous f g) : ReflTransGen Contiguous g f := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
    exact (ReflTransGen.single (fun s hs => by
      simpa only [Finset.union_comm] using hab s hs)).trans ih

private theorem simplicial_left {f g : Vertex K → Vertex L}
    (h : Contiguous f g) : Simplicial f := by
  intro s hs
  exact (L.isRelLowerSet_faces (h s hs)).2 Finset.subset_union_left
    ((K.isRelLowerSet_faces hs).1.attach.image _)

private def unionFaceMap {f g : Vertex K → Vertex L} (h : Contiguous f g) :
    Face K →o Face L where
  toFun s := ⟨faceImage f s.property ∪ faceImage g s.property, h s.val s.property⟩
  monotone' _ _ hab := Finset.union_subset_union
    (image_mono f _ _ hab) (image_mono g _ _ hab)

/-- The face maps of contiguously homotopic simplicial maps are joined by
a finite fence of order maps. -/
theorem face_map_fence {f g : Vertex K → Vertex L}
    (hf : Simplicial f) (hg : Simplicial g) (h : ReflTransGen Contiguous f g) :
    Relation.EqvGen (· ≤ ·) (faceMap f hf) (faceMap g hg) := by
  induction h with
  | refl => exact .refl _
  | tail _ hab ih =>
    let top := unionFaceMap hab
    have h₁ : faceMap _ (simplicial_left hab) ≤ top := fun _ => Finset.subset_union_left
    have h₂ : faceMap _ hg ≤ top := fun _ => Finset.subset_union_right
    exact .trans _ _ _ (ih (simplicial_left hab))
      (.trans _ _ _ (.rel _ _ h₁) (.symm _ _ (.rel _ _ h₂)))

private theorem lift_step [Finite X] {f g : Vertex K → Vertex L}
    (hf : Simplicial f) (hg : Simplicial g) (h : Contiguous f g) :
    ReflTransGen Contiguous (subdivide f hf) (subdivide g hg) := by
  let top := unionFaceMap h
  exact (reverse_chain (of_comparable top (faceMap f hf) (fun _ => Finset.subset_union_left))).trans
    (of_comparable top (faceMap g hg) (fun _ => Finset.subset_union_right))

/-- Ordinary subdivision preserves the contiguity class of a simplicial map. -/
theorem lift_chain [Finite X] {f g : Vertex K → Vertex L}
    (hf : Simplicial f) (hg : Simplicial g) (h : ReflTransGen Contiguous f g) :
    ReflTransGen Contiguous (subdivide f hf) (subdivide g hg) := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
    exact (ih (simplicial_left hab)).trans (lift_step (simplicial_left hab) hg hab)

/-- The ordinary iterates of two simplicial vertex maps remain in the same
contiguity class when the two originals are in that class. -/
theorem lift_iterates [Finite X] (f g : X → Y)
    (hf : ∀ s ∈ K, image s f ∈ L) (hg : ∀ s ∈ K, image s g ∈ L)
    (h : ReflTransGen Contiguous (ofTotal f hf) (ofTotal g hg)) (m : ℕ) :
    ReflTransGen Contiguous
      (ofTotal (iterate f hf m).val (iterate f hf m).property)
      (ofTotal (iterate g hg m).val (iterate g hg m).property) := by
  induction m with
  | zero => exact h
  | succ m ih =>
    have finite (k : ℕ) : Finite (iteratedAmbient K k).1 := by
      induction k with
      | zero => exact ‹Finite X›
      | succ k ih =>
        change Finite (Face (iteratedAmbient K k).2)
        letI := ih
        infer_instance
    letI : Finite (iteratedAmbient K m).1 := finite m
    have hlift := lift_chain
      (of_total_simplicial (iterate f hf m).val (iterate f hf m).property)
      (of_total_simplicial (iterate g hg m).val (iterate g hg m).property) ih
    rwa [subdivide_of_total, subdivide_of_total] at hlift

end

end D5.S3.Topology.StableCategory.OrdinaryContiguityLift
