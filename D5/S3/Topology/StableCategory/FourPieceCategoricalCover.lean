/- GID: D5/S3/Topology/StableCategory/FourPieceCategoricalCover
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/FourPieceCategoricalCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two categorical four-rank regions give four categorical pieces at a common depth. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.TetrahedralCategoricalCover
import D5.S3.Topology.StableCategory.TerminalCarrierIteration

/-! Assembly for Question 6.3 from two categorical induced colour regions.
The index of a collar is one less than its ambient subdivision depth.
All subdivision operations below advance source and target together. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.FourPieceCategoricalCover

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous faceImage sd skeleton vertexOfFace)
open BarycentricNeighborhoodIteration (iteratedAmbient subdivision subdivision_full)
open GraphSubdivisionIntervals (faceImage_singleton)
open OrdinaryCollarRetraction (colourComplex)
open OrdinarySubdivisionMap (cutFace iterate)
open OrdinaryContiguityLift (Simplicial ofTotal of_total_simplicial includeSubcomplex
  include_subcomplex_simplicial comp_chains subdivide subdivide_of_total lift_chain)
open TetrahedralCategoricalCover (meetingFaceComplex two_meeting_face_pieces_of_rank)
open ConnectedCategoryGraft (HasCategoricalCover)
open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open D5.S3.Geometry.FiniteConeUnionWedge (realizationInclusion)
open Relation (ReflTransGen)
open private image from D5.S3.Topology.OrdinarySubdivisionMap
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals
open private first from D5.S3.Topology.OrdinaryCollarRetraction
open private vertexIn mapCollar descending_collar_maps map_collar_simplicial
  from D5.S3.Topology.StableCategory.OrdinaryCollarContiguity
open private constant_face_image faceMap image_mono from
  D5.S3.Topology.StableCategory.OrdinaryContiguityLift
open private map_fence from D5.S3.Topology.SubdivisionCategoricalCover
open private subdivide_simplicial from
  D5.S3.Topology.StableCategory.TerminalCarrierIteration

noncomputable section

private def selectedColour {X : Type} (label : X → Fin 2) (i : Fin 2) (x : X) : Bool :=
  decide (label x = i)

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X
attribute [local instance] Classical.propDecidable

variable {U V W I : Type}
variable {K A : PreAbstractSimplicialComplex U}
variable {L : PreAbstractSimplicialComplex V} {M : PreAbstractSimplicialComplex W}

/-- A cover by subcomplexes, with categorical restrictions of a specified map. -/
def CategoricalMapCover (I : Type) (f : Vertex K → Vertex L) : Prop :=
  ∃ P : I → PreAbstractSimplicialComplex U, ∃ hP : ∀ i, P i ≤ K,
    (∀ s ∈ K, ∃ i, s ∈ P i) ∧
    ∀ i, ∃ c : Vertex L, ReflTransGen Contiguous
      (f ∘ includeSubcomplex (hP i)) (fun _ => c)

private theorem face_image_comp (f : Vertex K → Vertex L) (g : Vertex L → Vertex M)
    (s : Finset U) (hs : s ∈ K) (ht : faceImage f hs ∈ L) :
    faceImage (g ∘ f) hs = faceImage g ht := by
  ext y
  rw [mem_faceImage_iff, mem_faceImage_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨f u, (mem_faceImage_iff f hs _).mpr ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨u, hu, he⟩ := (mem_faceImage_iff f hs _).mp hv
    exact ⟨u, hu, congrArg (fun x : Vertex L => (g x).val) (Subtype.ext he)⟩

private theorem face_image_include (h : A ≤ K) (s : Finset U) (hs : s ∈ A) :
    faceImage (includeSubcomplex h) hs = s := by
  change s.attach.image Subtype.val = s
  exact Finset.attach_image_val

private theorem face_image_restrict (h : A ≤ K) (f : Vertex K → Vertex L)
    (s : Finset U) (hs : s ∈ A) :
    faceImage (f ∘ includeSubcomplex h) hs = faceImage f (h hs) := by
  ext y
  rw [mem_faceImage_iff, mem_faceImage_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨includeSubcomplex h u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    let a : Vertex A := ⟨u.val, (A.isRelLowerSet_faces hs).2
      (Finset.singleton_subset_iff.mpr hu) (Finset.singleton_nonempty _)⟩
    exact ⟨a, hu, rfl⟩

/-- An ambient flag in the subdivision of a subcomplex, read as a flag
of that subcomplex's own nonempty faces. -/
private def restrictFlag (K A : PreAbstractSimplicialComplex U) :
    Vertex (subdivision K A) → Vertex (sd A) :=
  fun v => vertexOfFace A ⟨v.val.val, v.property.2.2 _ (Finset.mem_singleton_self _)⟩

private theorem restrictFlag_simplicial (K A : PreAbstractSimplicialComplex U) :
    Simplicial (restrictFlag K A) := by
  intro s hs
  refine ⟨hs.1.attach.image _, ?_, fun a _ => a.property⟩
  intro a ha b hb hab
  obtain ⟨u, hu, rfl⟩ := (mem_faceImage_iff (restrictFlag K A) hs _).mp ha
  obtain ⟨v, hv, rfl⟩ := (mem_faceImage_iff (restrictFlag K A) hs _).mp hb
  have hne : u.val ≠ v.val := fun e => hab (congrArg (fun x => (restrictFlag K A x).val)
    (Subtype.ext e))
  exact hs.2.1 hu hv hne

private theorem subdivision_restrict (h : A ≤ K) (f : Vertex K → Vertex L)
    (hf : Simplicial f) :
    subdivide f hf ∘ includeSubcomplex (subdivision_full K A).1 =
      subdivide (f ∘ includeSubcomplex h) (hf.comp (include_subcomplex_simplicial h)) ∘
        restrictFlag K A := by
  funext v
  apply Subtype.ext
  apply Subtype.ext
  exact (face_image_restrict h f v.val.val
    (v.property.2.2 _ (Finset.mem_singleton_self _))).symm

private theorem subdivision_comp (f : Vertex K → Vertex L) (g : Vertex L → Vertex M)
    (hf : Simplicial f) (hg : Simplicial g) :
    subdivide (g ∘ f) (hg.comp hf) = subdivide g hg ∘ subdivide f hf := by
  funext v
  apply Subtype.ext
  apply Subtype.ext
  exact face_image_comp f g v.val.val v.val.property (hf _ v.val.property)

private theorem subdivision_const (c : Vertex L) (hc : Simplicial (fun _ : Vertex K => c)) :
    subdivide (fun _ : Vertex K => c) hc =
      (fun _ => vertexOfFace L ⟨{c.val}, c.property⟩) := by
  funext v
  apply Subtype.ext
  apply Subtype.ext
  exact constant_face_image c v.val.property

private theorem constant_simplicial (c : Vertex L) : Simplicial (fun _ : Vertex K => c) := by
  intro s hs
  rw [constant_face_image]
  exact c.property

/-- A categorical simplicial cover gives a categorical lower cover of the face poset. -/
theorem lower_cover_of_simplicial_cover {n : ℕ}
    (cover : CategoricalMapCover (Fin n) (id : Vertex K → Vertex K)) :
    HasCategoricalCover (Face K) n := by
  obtain ⟨P, hP, hc, hcat⟩ := cover
  let U (i : Fin n) : Set (Face K) := {s | s.val ∈ P i}
  refine ⟨U, ?_, fun s => hc s.val s.property⟩
  intro i
  refine ⟨fun s t hts hs => ((P i).isRelLowerSet_faces hs).2 hts
    (K.isRelLowerSet_faces t.property).1, ?_⟩
  obtain ⟨c, h⟩ := hcat i
  let pre : U i →o Face (P i) :=
    ⟨fun s => ⟨s.val.val, s.property⟩, fun _ _ hst => hst⟩
  let inc := faceMap (includeSubcomplex (hP i)) (include_subcomplex_simplicial (hP i))
  let con := faceMap (fun _ : Vertex (P i) => c) (constant_simplicial c)
  have hinc : inc.comp pre = (OrderEmbedding.subtype (U i)).toOrderHom := by
    apply OrderHom.ext
    funext s
    exact Subtype.ext (face_image_include (hP i) s.val.val s.property)
  have hcon : con.comp pre = OrderHom.const (U i) (⟨{c.val}, c.property⟩ : Face K) := by
    apply OrderHom.ext
    funext s
    exact Subtype.ext (constant_face_image c s.property)
  have hf : Relation.EqvGen (· ≤ ·) (inc.comp pre) (con.comp pre) :=
    map_fence (fun f : Face (P i) →o Face K => f.comp pre)
      (fun _ _ hfg => .rel _ _ (fun s => (OrderHom.le_def.mp hfg) (pre s)))
      (OrdinaryContiguityLift.face_map_fence (include_subcomplex_simplicial (hP i))
        (constant_simplicial c) h)
  rw [hinc, hcon] at hf
  exact ⟨_, hf⟩

private theorem id_simplicial : Simplicial (id : Vertex K → Vertex K) :=
  include_subcomplex_simplicial (le_refl K)

private theorem finite_at_depth [Finite U] (K : PreAbstractSimplicialComplex U) (n : ℕ) :
    Finite (iteratedAmbient K n).1 := by
  induction n with
  | zero => exact ‹Finite U›
  | succ n ih =>
    change Finite (Face (iteratedAmbient K n).2)
    letI := ih
    infer_instance

private theorem subdivision_covers [Finite U]
    (P : I → PreAbstractSimplicialComplex U) (hP : ∀ i, P i ≤ K)
    (hcover : ∀ s ∈ K, ∃ i, s ∈ P i) :
    ∀ s ∈ sd K, ∃ i, s ∈ subdivision K (P i) := by
  intro s hs
  obtain ⟨a, ha⟩ := hs.1
  obtain ⟨m, _, hm⟩ := Finite.exists_le_maximal (p := fun f : Face K => f ∈ s) ha
  have hgreatest (u : Face K) (hu : u ∈ s) : u ≤ m := by
    by_cases e : u = m
    · exact e.le
    rcases hs.2.1 hu hm.1 e with h | h
    · exact h.le
    · exact hm.2 hu h.le
  obtain ⟨i, hi⟩ := hcover m.val m.property
  exact ⟨i, hs.1, hs.2.1, fun u hu =>
    ((P i).isRelLowerSet_faces hi).2 (hgreatest u hu) (K.isRelLowerSet_faces u.property).1⟩

/-- A cover of a map persists after an ordinary subdivision of both
complexes. The new pieces are ambient flag subcomplexes. -/
private theorem cover_subdivide [Finite U] (f : Vertex K → Vertex L) (hf : Simplicial f)
    (h : CategoricalMapCover I f) : CategoricalMapCover I (subdivide f hf) := by
  obtain ⟨P, hP, hcover, hcat⟩ := h
  refine ⟨fun i => subdivision K (P i), fun i => (subdivision_full K (P i)).1,
    subdivision_covers P hP hcover, ?_⟩
  intro i
  obtain ⟨c, hc⟩ := hcat i
  let pre := restrictFlag K (P i)
  have hlift := lift_chain (hf.comp (include_subcomplex_simplicial (hP i)))
    (constant_simplicial (K := P i) c) hc
  have hpre := comp_chains pre id (restrictFlag_simplicial K (P i))
    (id_simplicial (K := sd L)) hlift
  refine ⟨vertexOfFace L ⟨{c.val}, c.property⟩, ?_⟩
  rw [subdivision_restrict (hP i) f hf]
  simpa only [Function.comp_def, id_eq, subdivision_const, pre] using hpre

/-- Pullback of a subcomplex along a map defined at actual vertices. -/
private def vertexPullback (f : Vertex K → Vertex L) (P : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex U where
  faces := {s | ∃ hs : s ∈ K, faceImage f hs ∈ P}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hp⟩
    refine ⟨(K.isRelLowerSet_faces hs).1, ?_⟩
    intro t hts ht
    let htK := (K.isRelLowerSet_faces hs).2 hts ht
    exact ⟨htK, (P.isRelLowerSet_faces hp).2 (image_mono f htK hs hts) (ht.attach.image _)⟩

private theorem pullback_le (f : Vertex K → Vertex L) (P : PreAbstractSimplicialComplex V) :
    vertexPullback f P ≤ K := by
  rintro s ⟨hs, _⟩
  exact hs

private def pullbackMap (f : Vertex K → Vertex L) (P : PreAbstractSimplicialComplex V) :
    Vertex (vertexPullback f P) → Vertex P := fun v =>
  ⟨(f (includeSubcomplex (pullback_le f P) v)).val, by
    obtain ⟨hs, hp⟩ := v.property
    rw [faceImage_singleton f (includeSubcomplex (pullback_le f P) v)] at hp
    exact hp⟩

private theorem pullbackMap_simplicial (f : Vertex K → Vertex L)
    (P : PreAbstractSimplicialComplex V) (hP : P ≤ L) :
    Simplicial (pullbackMap f P) := by
  intro s hs
  have he : faceImage (pullbackMap f P) hs = faceImage f (pullback_le f P hs) := by
    calc
      _ = faceImage (includeSubcomplex hP ∘ pullbackMap f P) hs := by rfl
      _ = faceImage f (pullback_le f P hs) := face_image_restrict (pullback_le f P) f s hs
  obtain ⟨_, hp⟩ := hs
  exact he.symm ▸ hp

/-- Pull back a categorical cover, including along maps which identify vertices. -/
private theorem cover_pullback (pre : Vertex K → Vertex L) (hpre : Simplicial pre)
    (f : Vertex L → Vertex M) (h : CategoricalMapCover I f) :
    CategoricalMapCover I (f ∘ pre) := by
  obtain ⟨P, hP, hcover, hcat⟩ := h
  refine ⟨fun i => vertexPullback pre (P i), fun i => pullback_le pre (P i), ?_, ?_⟩
  · intro s hs
    obtain ⟨i, hi⟩ := hcover _ (hpre s hs)
    exact ⟨i, hs, hi⟩
  · intro i
    obtain ⟨c, hc⟩ := hcat i
    refine ⟨c, ?_⟩
    have hchain := comp_chains (pullbackMap pre (P i)) id
      (pullbackMap_simplicial pre (P i) (hP i)) (id_simplicial (K := M)) hc
    change ReflTransGen Contiguous
      (id ∘ (f ∘ includeSubcomplex (hP i)) ∘ pullbackMap pre (P i))
      (id ∘ (fun _ => c) ∘ pullbackMap pre (P i))
    exact hchain

private theorem cover_of_chain {f g : Vertex K → Vertex L}
    (hfg : ReflTransGen Contiguous f g) (h : CategoricalMapCover I g) :
    CategoricalMapCover I f := by
  obtain ⟨P, hP, hcover, hcat⟩ := h
  refine ⟨P, hP, hcover, ?_⟩
  intro i
  obtain ⟨c, hc⟩ := hcat i
  have hh := comp_chains (includeSubcomplex (hP i)) id
    (include_subcomplex_simplicial (hP i)) (id_simplicial (K := L)) hfg
  have hh' : ReflTransGen Contiguous
      (f ∘ includeSubcomplex (hP i)) (g ∘ includeSubcomplex (hP i)) := by
    simpa only [Function.id_comp] using hh
  exact ⟨c, hh'.trans hc⟩

section Colours

variable {X : Type} [Fintype X] (K : PreAbstractSimplicialComplex X)
variable (label : X → Fin 2)

private abbrev region (i : Fin 2) := colourComplex K (selectedColour label i)

private theorem region_le (i : Fin 2) : region K label i ≤ K := fun _ hs => hs.1

private theorem include_image (i : Fin 2) : ∀ s ∈ region K label i, image s id ∈ K := by
  intro s hs
  simpa only [image, Finset.image_id] using hs.1

private abbrev regionMap (i : Fin 2) (n : ℕ) :=
  ofTotal (iterate id (include_image K label i) n).val
    (iterate id (include_image K label i) n).property

private theorem regionMap_simplicial (i : Fin 2) (n : ℕ) :
    Simplicial (regionMap K label i n) := of_total_simplicial _ _

private theorem regionMap_succ (i : Fin 2) (n : ℕ) :
    subdivide (regionMap K label i n) (regionMap_simplicial K label i n) =
      regionMap K label i (n + 1) :=
  subdivide_of_total _ _

private def collarAt (i : Fin 2) :
    (n : ℕ) → PreAbstractSimplicialComplex (iteratedAmbient K (n + 1)).1
  | 0 => meetingFaceComplex K (selectedColour label i)
  | n + 1 => subdivision (iteratedAmbient K (n + 1)).2 (collarAt i n)

private theorem collarAt_le (i : Fin 2) (n : ℕ) :
    collarAt K label i n ≤ (iteratedAmbient K (n + 1)).2 := by
  cases n with
  | zero => exact fun _ hs => hs.1
  | succ n => exact (subdivision_full _ _).1

private theorem collars_cover (n : ℕ) :
    ∀ s ∈ (iteratedAmbient K (n + 1)).2, ∃ i : Fin 2, s ∈ collarAt K label i n := by
  induction n with
  | zero =>
    intro s hs
    obtain ⟨a, ha⟩ := hs.1
    obtain ⟨m, _, hm⟩ := Finite.exists_le_minimal (p := fun f : Face K => f ∈ s) ha
    have hleast (u : Face K) (hu : u ∈ s) : m ≤ u := by
      by_cases e : m = u
      · exact e.le
      rcases hs.2.1 hm.1 hu e with h | h
      · exact h.le
      · exact hm.2 hu h.le
    obtain ⟨x, hx⟩ := (K.isRelLowerSet_faces m.property).1
    refine ⟨label x, hs, fun u hu => decide_eq_true ?_⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hleast u hu hx, by simp [selectedColour]⟩⟩
  | succ n ih =>
    letI := finite_at_depth K (n + 1)
    exact subdivision_covers (fun i => collarAt K label i n)
      (fun i => collarAt_le K label i n) ih

/-- The first colour cut and its iterates deform the ambient collar inclusion
to the composite through the region at exactly the same depth. -/
private theorem collar_factor (i : Fin 2) (n : ℕ) :
    ∃ cut : Vertex (collarAt K label i n) → Vertex (iteratedAmbient (region K label i) (n + 1)).2,
      Simplicial cut ∧ ReflTransGen Contiguous
        (includeSubcomplex (collarAt_le K label i n))
        (regionMap K label i (n + 1) ∘ cut) := by
  induction n with
  | zero =>
    let p := selectedColour label i
    let q (a : Face K) := decide (cutFace p a).Nonempty
    let cut : {a : Face K // q a = true} →o Face (region K label i) :=
      (first (K := K) p).comp ⟨fun a => ⟨a.val, of_decide_eq_true a.property⟩, fun _ _ h => h⟩
    let inc : {a : Face K // q a = true} →o Face K :=
      ⟨Subtype.val, fun _ _ h => h⟩
    let into : {a : Face K // q a = true} →o Face K :=
      (show Face (region K label i) →o Face K from
        ⟨fun a => ⟨a.val, a.property.1⟩, fun _ _ h => h⟩).comp cut
    have chain : ReflTransGen Contiguous (mapCollar q inc) (mapCollar q into) :=
      descending_collar_maps q inc into (fun _ => Finset.filter_subset _ _)
    refine ⟨mapCollar q cut, ?_, ?_⟩
    · intro s hs
      change faceImage (mapCollar q cut) hs ∈ sd (region K label i)
      simpa only [Finset.union_idempotent] using map_collar_simplicial q cut s hs
    · have hstart : mapCollar q inc = includeSubcomplex (collarAt_le K label i 0) := by
        funext v
        exact Subtype.ext rfl
      have hend : mapCollar q into = regionMap K label i 1 ∘ mapCollar q cut := by
        funext v
        apply Subtype.ext
        apply Subtype.ext
        change (cut (vertexIn v)).val = image (cut (vertexIn v)).val id
        rw [image, Finset.image_id]
      rwa [hstart, hend] at chain
  | succ n ih =>
    obtain ⟨cut, hcut, chain⟩ := ih
    let C := collarAt K label i n
    let L := (iteratedAmbient K (n + 1)).2
    let hCL := collarAt_le K label i n
    letI := finite_at_depth K (n + 1)
    let pre := restrictFlag L C
    let next := subdivide cut hcut ∘ pre
    have hnext : Simplicial next :=
      (subdivide_simplicial cut hcut).comp (restrictFlag_simplicial L C)
    have hlift := lift_chain (include_subcomplex_simplicial hCL)
      ((regionMap_simplicial K label i (n + 1)).comp hcut) chain
    have hh := comp_chains pre id (restrictFlag_simplicial L C)
      (id_simplicial (K := sd L)) hlift
    have hstart : subdivide (includeSubcomplex hCL) (include_subcomplex_simplicial hCL) ∘ pre =
        includeSubcomplex (collarAt_le K label i (n + 1)) := by
      have h := subdivision_restrict hCL (id : Vertex L → Vertex L) id_simplicial
      have hid : subdivide (id : Vertex L → Vertex L) id_simplicial = id := by
        funext v
        apply Subtype.ext
        apply Subtype.ext
        exact face_image_include (le_refl L) v.val.val v.val.property
      rw [hid] at h
      exact h.symm
    refine ⟨next, hnext, ?_⟩
    simpa only [Function.id_comp, hstart, subdivision_comp cut
      (regionMap K label i (n + 1)) hcut (regionMap_simplicial K label i (n + 1)),
      Function.comp_assoc, regionMap_succ, next] using hh

private theorem region_cover_later (i : Fin 2) {r n : ℕ} (hrn : r ≤ n)
    (h : CategoricalMapCover (Fin 2) (regionMap K label i (r + 1))) :
    CategoricalMapCover (Fin 2) (regionMap K label i (n + 1)) := by
  induction n, hrn using Nat.le_induction with
  | base => exact h
  | succ n hle ih =>
    letI := finite_at_depth (region K label i) (n + 1)
    rw [← regionMap_succ K label i (n + 1)]
    exact cover_subdivide _ (regionMap_simplicial K label i (n + 1)) ih

private theorem region_has_cover (i : Fin 2) (rank : X → Fin 4)
    (proper : ∀ s ∈ region K label i, Set.InjOn rank (s : Set X))
    (b : Vertex (region K label i)) (point : Space K)
    (contract : (realizationInclusion (region_le K label i)).Homotopy
      (ContinuousMap.const (Space (region K label i)) point))
    (connected : ∀ x y : Vertex K, (skeleton K).Reachable x y) :
    ∃ r, CategoricalMapCover (Fin 2) (regionMap K label i (r + 1)) := by
  obtain ⟨r, colour, hcover, cats⟩ :=
    two_meeting_face_pieces_of_rank (region_le K label i) rank proper b point contract connected
  let D := (iteratedAmbient (region K label i) r).2
  let P (j : Fin 2) := meetingFaceComplex D (fun x => decide (colour x = j))
  have hP (j : Fin 2) : P j ≤ sd D := fun _ hs => hs.1
  refine ⟨r, P, hP, ?_, ?_⟩
  · intro s hs
    have hs' : s ∈ P 0 ⊔ P 1 := hcover.symm ▸ hs
    rcases hs' with hs' | hs'
    · exact ⟨0, hs'⟩
    · exact ⟨1, hs'⟩
  · intro j
    obtain ⟨c, hc⟩ := cats j
    exact ⟨c, hc⟩

/-- Two induced categorical colour regions, each properly
four-coloured, have an actual cover by four categorical subcomplexes
after a finite number of ordinary subdivisions of the ambient complex.
The index consists of the outer colour and the relative piece number. -/
theorem four_pieces_of_two_categorical_colours
    (rank : Fin 2 → X → Fin 4)
    (proper : ∀ i, ∀ s ∈ region K label i, Set.InjOn (rank i) (s : Set X))
    (base : Vertex K) (point : Space K)
    (contract : ∀ i, (realizationInclusion (region_le K label i)).Homotopy
      (ContinuousMap.const (Space (region K label i)) point))
    (connected : ∀ x y : Vertex K, (skeleton K).Reachable x y) :
    ∃ n, CategoricalMapCover (Fin 2 × Fin 2)
      (id : Vertex (iteratedAmbient K n).2 → Vertex (iteratedAmbient K n).2) := by
  have ex : ∀ i, ∃ r, CategoricalMapCover (Fin 2) (regionMap K label i (r + 1)) := by
    intro i
    by_cases h : Nonempty (Vertex (region K label i))
    · obtain ⟨b⟩ := h
      exact region_has_cover K label i (rank i) (proper i) b point (contract i) connected
    · let D := sd (region K label i)
      refine ⟨0, fun _ => D, fun _ => le_refl _, fun _ hs => ⟨0, hs⟩, ?_⟩
      intro _
      let c := vertexOfFace K ⟨{base.val}, base.property⟩
      refine ⟨c, ?_⟩
      have eq : regionMap K label i 1 ∘ includeSubcomplex (le_refl D) =
          (fun _ => c) := by
        funext v
        obtain ⟨a, _⟩ := v.property.1
        obtain ⟨x, hx⟩ := ((region K label i).isRelLowerSet_faces a.property).1
        exact (h ⟨⟨x, ((region K label i).isRelLowerSet_faces a.property).2
          (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty _)⟩⟩).elim
      rw [eq]
  choose depth hdepth using ex
  let n := max (depth 0) (depth 1)
  have bound (i : Fin 2) : depth i ≤ n := by
    have hi : i = 0 ∨ i = 1 :=
      (Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp i.isLt)).imp Fin.ext Fin.ext
    rcases hi with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hc (i : Fin 2) : CategoricalMapCover (Fin 2)
      (includeSubcomplex (collarAt_le K label i n)) := by
    obtain ⟨cut, hp, chain⟩ := collar_factor K label i n
    have hr := region_cover_later K label i (bound i) (hdepth i)
    exact cover_of_chain chain (cover_pullback cut hp _ hr)
  unfold CategoricalMapCover at hc
  choose P hP hcover hcat using hc
  refine ⟨n + 1, fun ij => P ij.1 ij.2,
    fun ij => (hP ij.1 ij.2).trans (collarAt_le K label ij.1 n), ?_, ?_⟩
  · intro s hs
    obtain ⟨i, hi⟩ := collars_cover K label n s hs
    obtain ⟨j, hj⟩ := hcover i s hi
    exact ⟨(i, j), hj⟩
  · rintro ⟨i, j⟩
    exact hcat i j

end Colours
end
end D5.S3.Topology.StableCategory.FourPieceCategoricalCover
