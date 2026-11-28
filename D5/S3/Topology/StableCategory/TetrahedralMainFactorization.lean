/- GID: D5/S3/Topology/StableCategory/TetrahedralMainFactorization
   generality: I
   mirror-B: none(waiver:support-for-the-tetrahedral-refinement)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Main and extra regions give two parts of the tetrahedral refinement. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.OrdinaryCollarNaturality
import D5.S3.Topology.StableCategory.DisjointContiguityGluing
import D5.S3.Topology.RetractionCoordinate

/-! The two-colour refinement step in the tetrahedral construction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.TetrahedralMainFactorization

open BarycentricGraphDistance (Face Vertex oneSkeleton subdivisionGraph)
open BarycentricNeighborhoodIteration (iteratedAmbient iteratedSubcomplex subdivision_full)
open BarycentricBaseRigidity (Contiguous faceImage sd skeleton vertexOfFace)
open OrdinaryCollarRetraction (colourComplex retract)
open OrdinaryCollarContiguity (collarComplex collar_inclusion_contiguous)
open OrdinaryCollarNaturality (retractMap retract_map_simplicial pullback pullback_comparison)
open OrdinaryContiguityLift (Simplicial includeSubcomplex include_subcomplex_simplicial comp_chains
  comp_image constant_chain_of_reachable ofTotal of_total_simplicial)
open TetrahedronCollar16 (Color mainComplex hasColour main_conditions main_retraction_glued_refined
  Extra opposite pocket_conditions extra_retraction_in_subdivided_edge)
open OrdinarySubdivisionMap (inTwoCutCollar)
open DisjointContiguityGluing (glue_contiguity glue_simplicial)
open PathContiguity (intervalComplex IsIntervalMap relative_complex_contiguity)
open D5.S3.Geometry.FiniteAlexanderDualCollapse (simplex)
open GraphSubdivisionIntervals (faceImage_singleton)
open Relation (ReflTransGen)
open private forgetColour collarVertex from D5.S3.Topology.StableCategory.OrdinaryCollarContiguity
open private restricted_image from D5.S3.Topology.StableCategory.OrdinaryCollarNaturality
open private colourPiece glue from D5.S3.Topology.StableCategory.DisjointContiguityGluing
open private image from D5.S3.Topology.OrdinarySubdivisionMap
open private mem_faceImage_iff edge_chart interval_bound iterated_le_ambient simplex_le
  from D5.S3.Topology.GraphSubdivisionIntervals

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X
attribute [local instance] Classical.propDecidable

variable {X : Type} {K : PreAbstractSimplicialComplex X}

private def embedColour (p : X → Bool) :
    Vertex (iteratedAmbient (colourComplex K p) 3).2 →
      Vertex (iteratedAmbient K 3).2 :=
  fun v => vertexOfFace (sd (sd K)) ((forgetColour (K := K) p 3).val v.val)

private theorem embed_colour_simplicial (p : X → Bool) :
    Simplicial (embedColour (K := K) p) := by
  intro s hs
  have he : faceImage (embedColour (K := K) p) hs =
      s.image (forgetColour (K := K) p 3).val := by
    ext y
    rw [mem_faceImage_iff, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, h⟩
      exact ⟨x.val, hx, h⟩
    · rintro ⟨x, hx, h⟩
      have hv : ({x} : Finset _) ∈ (iteratedAmbient (colourComplex K p) 3).2 :=
        ((iteratedAmbient (colourComplex K p) 3).2.isRelLowerSet_faces hs).2
          (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty _)
      exact ⟨⟨x, hv⟩, hx, h⟩
  rw [he]
  exact (forgetColour (K := K) p 3).property _ hs

private theorem main_le_collar (colour : X → Fin 4) (c : Color) :
    mainComplex K colour c ≤ collarComplex K (hasColour c ∘ colour) := by
  intro s hs
  refine ⟨hs.1, fun v hv => decide_eq_true ?_⟩
  exact (RankColouredTetrahedron.row_inCollar colour c v).mp
    (main_conditions (of_decide_eq_true (hs.2 v hv))).1

/-- Within the selected colour graph, the retraction of the main region
is contiguous to a factorization through one further graph subdivision. -/
theorem main_retraction_factors [Finite X]
    (colour : X → Fin 4) (c : Color) (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X)) :
    let p := hasColour c ∘ colour
    let B := (iteratedAmbient (colourComplex K p) 3).2
    let P := mainComplex K colour c
    ∃ (select : Vertex (sd B) → Vertex B) (factor : Vertex P → Vertex (sd B)),
      (∀ v, (select v).val ∈ v.val.val) ∧ Simplicial select ∧ Simplicial factor ∧
      ReflTransGen Contiguous
        (retractMap p ∘ includeSubcomplex (main_le_collar colour c)) (select ∘ factor) := by
  intro p B P
  haveI : Finite (iteratedAmbient K 3).1 := by
    change Finite (Face (sd (sd K)))
    infer_instance
  obtain ⟨select, factor, hselect, hselectFace, hfactor, hlocal⟩ :=
    main_retraction_glued_refined (K := K) colour c hinj
  exact ⟨select, factor, hselect, hselectFace, hfactor, hlocal⟩

/-- The main part of the third subdivision factors, up to contiguity in the
unchanged ambient subdivision, through a fourth subdivision of its colour graph. -/
theorem main_inclusion_factors_through_refinement [Finite X]
    (colour : X → Fin 4) (c : Color) (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X)) :
    let A := colourComplex K (hasColour c ∘ colour)
    let B := (iteratedAmbient A 3).2
    let P := mainComplex K colour c
    ∃ (select : Vertex (sd B) → Vertex B) (factor : Vertex P → Vertex (sd B)),
      (∀ v, (select v).val ∈ v.val.val) ∧ Simplicial select ∧ Simplicial factor ∧
      ReflTransGen Contiguous (fun v : Vertex P => ⟨v.val, v.property.1⟩)
        (embedColour (K := K) (hasColour c ∘ colour) ∘ select ∘ factor) := by
  intro A B P
  let p := hasColour c ∘ colour
  let J := (iteratedAmbient K 3).2
  haveI : Finite (Face K) := inferInstance
  haveI : Finite (Face (sd K)) := inferInstance
  haveI : Finite (iteratedAmbient K 3).1 := by
    change Finite (Face (sd (sd K)))
    infer_instance
  let intoCollar := includeSubcomplex (main_le_collar (K := K) colour c)
  have hpre := include_subcomplex_simplicial (main_le_collar (K := K) colour c)
  have hIdJ : Simplicial (id : Vertex J → Vertex J) :=
    include_subcomplex_simplicial (le_refl J)
  have hIdP : Simplicial (id : Vertex P → Vertex P) :=
    include_subcomplex_simplicial (le_refl P)
  obtain ⟨select, factor, hselect, hselectFace, hfactor, hlocal⟩ :=
    main_retraction_factors (K := K) colour c hinj
  have hfirst := comp_chains intoCollar id hpre hIdJ
    (collar_inclusion_contiguous (K := K) p)
  have hsecond := comp_chains id (embedColour (K := K) p) hIdP
    (embed_colour_simplicial (K := K) p) hlocal
  exact ⟨select, factor, hselect, hselectFace, hfactor, hfirst.trans hsecond⟩

private theorem contracts_in_subdivided_edge {U : Type}
    {P : PreAbstractSimplicialComplex U} [Finite (Vertex P)]
    (A : PreAbstractSimplicialComplex X) (e : Finset X) (he : e ∈ A) (he₂ : e.card = 2)
    (f : Vertex P → Vertex (iteratedAmbient A 3).2)
    (hface : ∀ s (hs : s ∈ P), faceImage f hs ∈ iteratedSubcomplex A (simplex e) 3) :
    ∃ b, ReflTransGen Contiguous f (fun _ => b) := by
  obtain ⟨x, y, hxy, heq⟩ := Finset.card_eq_two.mp he₂
  subst e
  let x' : Vertex A := ⟨x, (A.isRelLowerSet_faces he).2
    (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)) (Finset.singleton_nonempty _)⟩
  let y' : Vertex A := ⟨y, (A.isRelLowerSet_faces he).2 (Finset.singleton_subset_iff.mpr
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) (Finset.singleton_nonempty _)⟩
  obtain ⟨chart, hinj, _, hchart⟩ := edge_chart x' y' (fun h => hxy (congrArg Subtype.val h)) he 3
  have covered (u : Vertex P) :
      ∃ i : Vertex (intervalComplex 8), chart i = f u := by
    have h := hface {u.val} u.property
    rw [faceImage_singleton] at h
    obtain ⟨t, ht, hEq⟩ := (hchart _).mp h
    have hu : (f u).val ∈ faceImage chart ht := hEq.symm ▸ Finset.mem_singleton_self _
    obtain ⟨i, _, h⟩ := (mem_faceImage_iff chart ht _).mp hu
    exact ⟨i, Subtype.ext h⟩
  choose coordinate hc using covered
  have index_mem (s : Finset U) (hs : s ∈ P) (t : Finset ℕ) (ht : t ∈ intervalComplex 8)
      (h : faceImage chart ht = faceImage f hs) (u : Vertex P) (hu : u.val ∈ s) :
      (coordinate u).val ∈ t := by
    have hv : (f u).val ∈ faceImage f hs := (mem_faceImage_iff f hs _).mpr ⟨u, hu, rfl⟩
    rw [← h] at hv
    obtain ⟨j, hj, hEq⟩ := (mem_faceImage_iff chart ht _).mp hv
    have hjeq := hinj ((Subtype.ext hEq : chart j = f u).trans (hc u).symm)
    exact hjeq ▸ hj
  let zero : Vertex (intervalComplex 8) := ⟨0, Finset.singleton_nonempty _, by
    simp⟩
  have hi : IsIntervalMap (oneSkeleton P) 8 (fun x => (coordinate x).val) := by
    refine ⟨fun u => interval_bound (coordinate u), ?_⟩
    intro u v huv
    obtain ⟨t, ht, hEq⟩ := (hchart _).mp (hface _ huv.2)
    have hu := index_mem _ huv.2 t ht hEq u (Finset.mem_insert_self _ _)
    have hv := index_mem _ huv.2 t ht hEq v
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    exact ⟨ht.2.2 _ hu _ hv, ht.2.2 _ hv _ hu⟩
  have hz : IsIntervalMap (oneSkeleton P) 8 (fun _ => zero.val) :=
    ⟨fun _ => interval_bound zero, fun {_ _} _ => ⟨Nat.le_succ _, Nat.le_succ _⟩⟩
  have chain := relative_complex_contiguity 8 ∅ (f := coordinate) (g := fun _ => zero)
    hi hz (by intro u hu; exact False.elim hu)
  have hchartSimplicial : Simplicial chart := fun s hs =>
    iterated_le_ambient (simplex_le he) 3 ((hchart _).mpr ⟨s, hs, rfl⟩)
  have hId : Simplicial (id : Vertex P → Vertex P) :=
    include_subcomplex_simplicial (le_refl P)
  refine ⟨chart zero, ?_⟩
  have chain' : ReflTransGen Contiguous coordinate (fun _ => zero) :=
    ReflTransGen.mono (fun _ _ h => h.1) _ _ chain
  have h := comp_chains id chart hId hchartSimplicial chain'
  have hEq : chart ∘ coordinate ∘ id = f := funext hc
  exact hEq ▸ h

private abbrev ExtraVertex (K : PreAbstractSimplicialComplex X) (colour : X → Fin 4) (c : Color) :=
  {w : Face (iteratedAmbient K 2).2 | Extra c (RankColouredTetrahedron.row colour w)}

private def extraGraph (K : PreAbstractSimplicialComplex X) (colour : X → Fin 4) (c : Color) :=
  (subdivisionGraph (iteratedAmbient K 2).2).induce
    {w | Extra c (RankColouredTetrahedron.row colour w)}

private abbrev PieceIndex (K : PreAbstractSimplicialComplex X) (colour : X → Fin 4)
    (c : Color) :=
  Option (extraGraph K colour c).ConnectedComponent

private def pieceIndex (colour : X → Fin 4) (c : Color)
    (v : Face (iteratedAmbient K 2).2) : PieceIndex K colour c :=
  if h : Extra c (RankColouredTetrahedron.row colour v) then
    some ((extraGraph K colour c).connectedComponentMk ⟨v, h⟩)
  else none

private theorem same_piece_of_same_colour (colour : X → Fin 4) (c : Color)
    {u v : Face (iteratedAmbient K 2).2}
    (hu : (TetrahedronCollar16.label (RankColouredTetrahedron.row colour u)).color = c)
    (hv : (TetrahedronCollar16.label (RankColouredTetrahedron.row colour v)).color = c)
    (h : (subdivisionGraph (iteratedAmbient K 2).2).Adj u v) :
    pieceIndex colour c u = pieceIndex colour c v := by
  have isMain (w : Face (iteratedAmbient K 2).2)
      (hc : (TetrahedronCollar16.label (RankColouredTetrahedron.row colour w)).color = c)
      (hex : ¬ Extra c (RankColouredTetrahedron.row colour w)) :
      TetrahedronCollar16.Main c (RankColouredTetrahedron.row colour w) := by
    refine ⟨hc, ?_⟩
    cases he : (TetrahedronCollar16.label (RankColouredTetrahedron.row colour w)).height with
    | none => exact (hex ⟨hc, he⟩).elim
    | some k => simp [he]
  by_cases eu : Extra c (RankColouredTetrahedron.row colour u)
  · by_cases ev : Extra c (RankColouredTetrahedron.row colour v)
    · simpa only [pieceIndex, dif_pos eu, dif_pos ev, Option.some.injEq] using
        (SimpleGraph.ConnectedComponent.sound
          ((show (extraGraph K colour c).Adj ⟨u, eu⟩ ⟨v, ev⟩ from h).reachable))
    · exact (RankColouredTetrahedron.main_extra_separated colour (isMain v hv ev) eu h.symm).elim
  · by_cases ev : Extra c (RankColouredTetrahedron.row colour v)
    · exact (RankColouredTetrahedron.main_extra_separated colour (isMain u hu eu) ev h).elim
    · simp only [pieceIndex, dif_neg eu, dif_neg ev]

/-- Every same-colour face of the third subdivision lies in the main
region or in one connected extra component. -/
private theorem single_piece_face (colour : X → Fin 4) (c : Color)
    (s : Finset (Face (iteratedAmbient K 2).2)) (hs : s ∈ (iteratedAmbient K 3).2)
    (hc : ∀ v ∈ s, (TetrahedronCollar16.label (RankColouredTetrahedron.row colour v)).color = c) :
    ∃ j, ∀ v ∈ s, pieceIndex colour c v = j := by
  obtain ⟨u, hu⟩ := hs.1
  refine ⟨pieceIndex colour c u, fun v hv => ?_⟩
  by_cases h : v = u
  · exact congrArg (pieceIndex colour c) h
  · exact same_piece_of_same_colour colour c (hc v hv) (hc u hu) (hs.2.1 hv hu h)

/-- The full subcomplex on a connected component of the extra vertices. -/
def extraComponent (K : PreAbstractSimplicialComplex X) (colour : X → Fin 4) (c : Color)
    (u : ExtraVertex K colour c) : PreAbstractSimplicialComplex (iteratedAmbient K 3).1 :=
  colourComplex (iteratedAmbient K 3).2 fun v =>
    decide (∃ h : Extra c (RankColouredTetrahedron.row colour v),
      (extraGraph K colour c).Reachable u ⟨v, h⟩)

private theorem extra_le_collar (colour : X → Fin 4) (c : Color)
    (u : ExtraVertex K colour c) :
    extraComponent K colour c u ≤ collarComplex K (hasColour (opposite c) ∘ colour) := by
  intro s hs
  refine ⟨hs.1, fun v hv => decide_eq_true ?_⟩
  have witness :
      ∃ h : Extra c (RankColouredTetrahedron.row colour v),
        (extraGraph K colour c).Reachable u ⟨v, h⟩ := of_decide_eq_true (hs.2 v hv)
  obtain ⟨h, _⟩ := witness
  exact (RankColouredTetrahedron.row_inCollar colour (opposite c) v).mp (pocket_conditions h).1

/-- An extra component retracts into a single opposite-colour old edge.
The contraction takes place before mapping from that colour graph to
the ambient complex. -/
theorem extra_retraction_contracts [Finite X] (colour : X → Fin 4) (c : Color)
    (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X)) (u : ExtraVertex K colour c) :
    let p := hasColour (opposite c) ∘ colour
    ∃ b, ReflTransGen Contiguous
      (retractMap p ∘ includeSubcomplex (extra_le_collar colour c u)) (fun _ => b) := by
  intro p
  let P := extraComponent K colour c u
  let A := colourComplex K p
  let B := (iteratedAmbient A 3).2
  let inc := includeSubcomplex (extra_le_collar colour c u)
  let r : Vertex P → Vertex B := retractMap p ∘ inc
  haveI : Finite (iteratedAmbient K 3).1 := by
    change Finite (Face (sd (sd K)))
    infer_instance
  obtain ⟨e, he, he₂, heRetract⟩ := extra_retraction_in_subdivided_edge colour hinj c u
  have hsupp (v : Vertex P) : {(r v).val} ∈ iteratedSubcomplex A (simplex e) 3 := by
    have hv : ∃ h : Extra c (RankColouredTetrahedron.row colour v.val),
        (extraGraph K colour c).Reachable u ⟨v.val, h⟩ :=
      of_decide_eq_true (v.property.2 _ (Finset.mem_singleton_self _))
    obtain ⟨h, hreach⟩ := hv
    exact heRetract ⟨v.val, h⟩ hreach (collarVertex p (inc v)).property
  have hface (s : Finset _) (hs : s ∈ P) :
      faceImage r hs ∈ iteratedSubcomplex A (simplex e) 3 := by
    have hr : Simplicial r := by
      intro t ht
      have heq : faceImage r ht =
          faceImage (retractMap p) (extra_le_collar colour c u ht) := by
        unfold faceImage
        exact Finset.image_congr fun v _ => rfl
      rw [heq]
      exact retract_map_simplicial p _ _
    have hbase : faceImage r hs ∈ B := hr s hs
    exact (subdivision_full _ _).2 ⟨_, hbase⟩ (fun a ha => by
      obtain ⟨v, _, rfl⟩ := (mem_faceImage_iff r hs a).mp ha
      exact hsupp v)
  exact contracts_in_subdivided_edge A e he he₂ r hface

/-- Every connected extra region contracts in the fixed ambient third subdivision. -/
theorem extra_component_categorical [Finite X] (colour : X → Fin 4) (c : Color)
    (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X)) (u : ExtraVertex K colour c) :
    let P := extraComponent K colour c u
    ∃ b, ReflTransGen Contiguous (fun v : Vertex P => ⟨v.val, v.property.1⟩) (fun _ => b) := by
  intro P
  let p := hasColour (opposite c) ∘ colour
  let J := (iteratedAmbient K 3).2
  let hle := extra_le_collar colour c u
  let inc := includeSubcomplex hle
  have hpre := include_subcomplex_simplicial hle
  have hId : Simplicial (id : Vertex J → Vertex J) :=
    include_subcomplex_simplicial (le_refl J)
  have hfirst := comp_chains inc id hpre hId (collar_inclusion_contiguous (K := K) p)
  obtain ⟨b, hsecond⟩ := extra_retraction_contracts colour c hinj u
  have hIdP : Simplicial (id : Vertex P → Vertex P) :=
    include_subcomplex_simplicial (le_refl P)
  exact ⟨embedColour (K := K) p b, hfirst.trans
    (comp_chains id (embedColour (K := K) p) hIdP (embed_colour_simplicial (K := K) p) hsecond)⟩

section Pullback

open OrdinarySubdivisionMap (iterate)

variable {U Z : Type} {D : PreAbstractSimplicialComplex U} {L : PreAbstractSimplicialComplex Z}
variable [Finite U] [Finite X]
variable (i : U → Z) (hi : ∀ s ∈ D, image s i ∈ L)
variable (f : U → X) (hf : ∀ s ∈ D, image s f ∈ K)
variable (colour : X → Fin 4) (c : Color) (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X))
variable (g : X → Z)

/-- The colour of a vertex read by pulling back the chamber partition. -/
def refinedColour (v : (iteratedAmbient D 3).1) : Color :=
  (TetrahedronCollar16.label (RankColouredTetrahedron.row colour ((iterate f hf 3).val v))).color

private def refinedColourComplex :=
  colourComplex (iteratedAmbient D 3).2 (fun v => decide (refinedColour f hf colour v = c))

private def refinedPieceIndex (v : (iteratedAmbient D 3).1) : PieceIndex K colour c :=
  pieceIndex colour c ((iterate f hf 3).val v)

private theorem refined_colour_face_in_one_piece (s : Finset (iteratedAmbient D 3).1)
    (hs : s ∈ refinedColourComplex f hf colour c) :
    ∃ j, ∀ v ∈ s, refinedPieceIndex f hf colour c v = j := by
  let map := iterate f hf 3
  have hcolour (y : (iteratedAmbient K 3).1) (hy : y ∈ image s map.val) :
      (TetrahedronCollar16.label (RankColouredTetrahedron.row colour y)).color = c := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact of_decide_eq_true (hs.2 x hx)
  obtain ⟨j, hj⟩ := single_piece_face colour c _ (map.property s hs.1) hcolour
  exact ⟨j, fun x hx => hj _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩

private theorem refined_main (s : Finset (iteratedAmbient D 3).1)
    (hs : s ∈ (iteratedAmbient D 3).2) :
    s ∈ pullback (iteratedAmbient D 3).2 (iterate f hf 3).val (mainComplex K colour c) ↔
    s ∈ refinedColourComplex f hf colour c ∧
      ∀ v ∈ s, refinedPieceIndex f hf colour c v = none := by
  let map := (iterate f hf 3).val
  have vertex_iff (v : (iteratedAmbient D 3).1) :
      TetrahedronCollar16.Main c (RankColouredTetrahedron.row colour (map v)) ↔
        refinedColour f hf colour v = c ∧ refinedPieceIndex f hf colour c v = none := by
    let row := RankColouredTetrahedron.row colour (map v)
    change TetrahedronCollar16.Main c row ↔ (TetrahedronCollar16.label row).color = c ∧
      pieceIndex colour c (map v) = none
    constructor
    · intro hm
      have hne : ¬ Extra c row := by
        intro he
        have hk := hm.2
        rw [he.2] at hk
        contradiction
      exact ⟨hm.1, dif_neg hne⟩
    · rintro ⟨hc, hp⟩
      refine ⟨hc, ?_⟩
      cases h : (TetrahedronCollar16.label row).height with
      | none =>
        have he : Extra c row := ⟨hc, h⟩
        change (if e : Extra c row then some ((extraGraph K colour c).connectedComponentMk
          ⟨map v, e⟩) else none) = none at hp
        rw [dif_pos he] at hp
        contradiction
      | some k => simp [h]
  constructor
  · intro hp
    have hv (v) (hv : v ∈ s) := (vertex_iff v).1
      (of_decide_eq_true (hp.2.2 _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)))
    exact ⟨⟨hs, fun v hv' => decide_eq_true (hv v hv').1⟩, fun v hv' => (hv v hv').2⟩
  · rintro ⟨hc, he⟩
    refine ⟨hs, (iterate f hf 3).property s hs, ?_⟩
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact decide_eq_true ((vertex_iff v).2 ⟨of_decide_eq_true (hc.2 v hv), he v hv⟩)

private theorem refined_extra (u : ExtraVertex K colour c) (s : Finset (iteratedAmbient D 3).1)
    (hs : s ∈ (iteratedAmbient D 3).2) :
    s ∈ pullback (iteratedAmbient D 3).2 (iterate f hf 3).val (extraComponent K colour c u) ↔
    s ∈ refinedColourComplex f hf colour c ∧
      ∀ v ∈ s, refinedPieceIndex f hf colour c v =
        some ((extraGraph K colour c).connectedComponentMk u) := by
  let map := (iterate f hf 3).val
  have vertex_iff (v : (iteratedAmbient D 3).1) :
      (∃ h : Extra c (RankColouredTetrahedron.row colour (map v)),
        (extraGraph K colour c).Reachable u ⟨map v, h⟩) ↔
      refinedColour f hf colour v = c ∧ refinedPieceIndex f hf colour c v =
        some ((extraGraph K colour c).connectedComponentMk u) := by
    by_cases he : Extra c (RankColouredTetrahedron.row colour (map v))
    · simp only [refinedPieceIndex, pieceIndex, map, dif_pos he, Option.some.injEq]
      exact ⟨fun ⟨h, hreach⟩ => ⟨h.1, SimpleGraph.ConnectedComponent.sound hreach.symm⟩,
        fun ⟨_, hEq⟩ => ⟨he, (SimpleGraph.ConnectedComponent.exact hEq).symm⟩⟩
    · simp [refinedPieceIndex, pieceIndex, map, he]
  constructor
  · intro hp
    have hv (v) (hv : v ∈ s) := (vertex_iff v).1
      (of_decide_eq_true (hp.2.2 _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)))
    exact ⟨⟨hs, fun v hv' => decide_eq_true (hv v hv').1⟩, fun v hv' => (hv v hv').2⟩
  · rintro ⟨hc, he⟩
    refine ⟨hs, (iterate f hf 3).property s hs, ?_⟩
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact decide_eq_true ((vertex_iff v).2 ⟨of_decide_eq_true (hc.2 v hv), he v hv⟩)

/-- The pulled-back main region factors through the fourth subdivision
of the selected graph while the ambient is subdivided only three times. -/
theorem pullback_main_factorization
    (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X))
    (hg : ∀ s ∈ colourComplex K (hasColour c ∘ colour), image s g ∈ L)
    (old : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D ((hasColour c ∘ colour) ∘ f)) i (fun s hs => hi s hs.1))
      (ofTotal (g ∘ f) (comp_image f
        (restricted_image f hf ((hasColour c ∘ colour) ∘ f) (hasColour c ∘ colour)
          (fun _ => rfl)) g hg))) :
    let B := (iteratedAmbient (colourComplex K (hasColour c ∘ colour)) 3).2
    let P := pullback (iteratedAmbient D 3).2 (iterate f hf 3).val (mainComplex K colour c)
    ∃ (select : Vertex (sd B) → Vertex B) (factor : Vertex P → Vertex (sd B)),
      (∀ v, (select v).val ∈ v.val.val) ∧ Simplicial select ∧ Simplicial factor ∧
      ReflTransGen Contiguous
        (ofTotal (K := P) (iterate i hi 3).val (fun s hs => (iterate i hi 3).property s hs.1))
        (ofTotal (iterate g hg 3).val (iterate g hg 3).property ∘ select ∘ factor) := by
  intro B P
  obtain ⟨select, factor, hmember, hselect, hfactor, hchain⟩ :=
    main_retraction_factors colour c hinj
  let pre := ofTotal (K := P) (iterate f hf 3).val (fun _ hs => hs.2)
  refine ⟨select, factor ∘ pre, hmember, hselect,
    hfactor.comp (of_total_simplicial _ _), ?_⟩
  exact pullback_comparison i hi f hf (hasColour c ∘ colour) g hg old
    (main_le_collar colour c) (select ∘ factor) hchain

/-- The pulled-back extra component contracts via the opposite graph.
Its constant value lies in the same fixed ambient third subdivision. -/
theorem pullback_extra_contracts (u : ExtraVertex K colour c)
    (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X))
    (hg : ∀ s ∈ colourComplex K (hasColour (opposite c) ∘ colour), image s g ∈ L)
    (old : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D ((hasColour (opposite c) ∘ colour) ∘ f)) i
        (fun s hs => hi s hs.1))
      (ofTotal (g ∘ f) (comp_image f
        (restricted_image f hf ((hasColour (opposite c) ∘ colour) ∘ f)
          (hasColour (opposite c) ∘ colour) (fun _ => rfl)) g hg))) :
    let P := pullback (iteratedAmbient D 3).2 (iterate f hf 3).val (extraComponent K colour c u)
    ∃ b, ReflTransGen Contiguous
      (ofTotal (K := P) (iterate i hi 3).val (fun s hs => (iterate i hi 3).property s hs.1))
      (fun _ => b) := by
  intro P
  obtain ⟨b, hchain⟩ := extra_retraction_contracts colour c hinj u
  exact ⟨ofTotal (iterate g hg 3).val (iterate g hg 3).property b,
    pullback_comparison i hi f hf (hasColour (opposite c) ∘ colour) g hg old
      (extra_le_collar colour c u) (fun _ => b) hchain⟩

/-- One refinement step factors through the fourth subdivision of the same
colour graph. In a connected target, all extra components may use the
same chosen parameter vertex. -/
theorem refine_colour_factorization (gOpp : X → Z)
    (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X))
    (hg : ∀ s ∈ colourComplex K (hasColour c ∘ colour), image s g ∈ L)
    (hgOpp : ∀ s ∈ colourComplex K (hasColour (opposite c) ∘ colour), image s gOpp ∈ L)
    (old : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D ((hasColour c ∘ colour) ∘ f)) i (fun s hs => hi s hs.1))
      (ofTotal (g ∘ f) (comp_image f
        (restricted_image f hf ((hasColour c ∘ colour) ∘ f) (hasColour c ∘ colour)
          (fun _ => rfl)) g hg)))
    (oldOpp : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D ((hasColour (opposite c) ∘ colour) ∘ f)) i
        (fun s hs => hi s hs.1))
      (ofTotal (gOpp ∘ f) (comp_image f
        (restricted_image f hf ((hasColour (opposite c) ∘ colour) ∘ f)
          (hasColour (opposite c) ∘ colour) (fun _ => rfl)) gOpp hgOpp))) :
    let B := (iteratedAmbient (colourComplex K (hasColour c ∘ colour)) 3).2
    let C := (iteratedAmbient L 3).2
    let P := refinedColourComplex f hf colour c
    ∀ (anchor : Vertex (sd B)) (connected : ∀ a b : Vertex C, (skeleton C).Reachable a b),
      ∃ (select : Vertex (sd B) → Vertex B) (factor : Vertex P → Vertex (sd B)),
        (∀ v, (select v).val ∈ v.val.val) ∧ Simplicial select ∧ Simplicial factor ∧
        ReflTransGen Contiguous
          (ofTotal (K := P) (iterate i hi 3).val (fun s hs => (iterate i hi 3).property s hs.1))
          (ofTotal (iterate g hg 3).val (iterate g hg 3).property ∘ select ∘ factor) := by
  intro B C P anchor connected
  let label := refinedPieceIndex f hf colour c
  let piece := colourPiece (P := P) label
  let initial := ofTotal (K := P) (iterate i hi 3).val (fun s hs => (iterate i hi 3).property s hs.1)
  have hmain : piece none =
      pullback (iteratedAmbient D 3).2 (iterate f hf 3).val (mainComplex K colour c) := by
    apply le_antisymm
    · intro s hs
      exact (refined_main f hf colour c s hs.1.1).2
        ⟨hs.1, fun v hv => of_decide_eq_true (hs.2 v hv)⟩
    · intro s hs
      have h := (refined_main f hf colour c s hs.1).1 hs
      exact ⟨h.1, fun v hv => decide_eq_true (h.2 v hv)⟩
  have hextra (u : ExtraVertex K colour c) :
      piece (some ((extraGraph K colour c).connectedComponentMk u)) =
        pullback (iteratedAmbient D 3).2 (iterate f hf 3).val (extraComponent K colour c u) := by
    apply le_antisymm
    · intro s hs
      exact (refined_extra f hf colour c u s hs.1.1).2
        ⟨hs.1, fun v hv => of_decide_eq_true (hs.2 v hv)⟩
    · intro s hs
      have h := (refined_extra f hf colour c u s hs.1).1 hs
      exact ⟨h.1, fun v hv => decide_eq_true (h.2 v hv)⟩
  let inc (j : PieceIndex K colour c) : Vertex (piece j) → Vertex C :=
    fun v => initial ⟨v.val, v.property.1⟩
  let post := ofTotal (iterate g hg 3).val (iterate g hg 3).property
  have main : ∃ (select : Vertex (sd B) → Vertex B) (factor : Vertex (piece none) → Vertex (sd B)),
      (∀ v, (select v).val ∈ v.val.val) ∧ Simplicial select ∧ Simplicial factor ∧
      ReflTransGen Contiguous (inc none) (post ∘ select ∘ factor) := by
    obtain ⟨select, factor, hmember, hselect, hfactor, hchain⟩ :=
      pullback_main_factorization i hi f hf colour c g hinj hg old
    let pre := includeSubcomplex hmain.le
    have hpre := include_subcomplex_simplicial hmain.le
    exact ⟨select, factor ∘ pre, hmember, hselect, hfactor.comp hpre,
      comp_chains pre (id : Vertex C → Vertex C) hpre
        (include_subcomplex_simplicial (le_refl C)) hchain⟩
  have extra (e : (extraGraph K colour c).ConnectedComponent) :
      ∃ v : Vertex C, ReflTransGen Contiguous (inc (some e)) (fun _ => v) := by
    induction e using SimpleGraph.ConnectedComponent.ind with
    | h u =>
      let eu : ExtraVertex K colour c := ⟨u.val, u.property⟩
      obtain ⟨v, hchain⟩ :=
        pullback_extra_contracts i hi f hf colour c gOpp eu hinj hgOpp oldOpp
      let pre := includeSubcomplex (hextra eu).le
      exact ⟨v, comp_chains pre (id : Vertex C → Vertex C)
        (include_subcomplex_simplicial (hextra eu).le)
        (include_subcomplex_simplicial (le_refl C)) hchain⟩
  obtain ⟨select, mainFactor, hmember, hselect, hmainFactor, hmainChain⟩ := main
  let factor (j : PieceIndex K colour c) : Vertex (piece j) → Vertex (sd B) :=
    match j with
    | none => mainFactor
    | some _ => fun _ => anchor
  have hfactor (j : PieceIndex K colour c) : Simplicial (factor j) := by
    cases j with
    | none => exact hmainFactor
    | some e =>
      intro s hs
      change s.attach.image (fun _ => anchor.val) ∈ sd B
      rw [Finset.image_const ((piece (some e)).isRelLowerSet_faces hs).1.attach]
      exact anchor.property
  have hchain (j : PieceIndex K colour c) :
      ReflTransGen Contiguous (inc j) (post ∘ select ∘ factor j) := by
    cases j with
    | none => exact hmainChain
    | some e =>
      obtain ⟨v, hv⟩ := extra e
      exact hv.trans (constant_chain_of_reachable (connected v (post (select anchor))))
  letI : Finite (Face K) := Finite.of_injective Subtype.val
    (Subtype.val_injective : Function.Injective (Subtype.val : Face K → Finset X))
  letI : Finite (Face (sd K)) := Finite.of_injective Subtype.val
    (Subtype.val_injective : Function.Injective (Subtype.val : Face (sd K) → Finset (Face K)))
  letI : Finite (iteratedAmbient K 2).1 := inferInstanceAs (Finite (Face (sd K)))
  letI : Finite (Face (iteratedAmbient K 2).2) := Finite.of_injective Subtype.val
    (Subtype.val_injective : Function.Injective
      (Subtype.val : Face (sd (sd K)) → Finset (Face (sd K))))
  letI : Finite (ExtraVertex K colour c) :=
    Finite.of_injective Subtype.val
      (Subtype.val_injective : Function.Injective
        (Subtype.val : ExtraVertex K colour c → Face (sd (sd K))))
  haveI : Finite (extraGraph K colour c).ConnectedComponent := by
    change Finite (Quot (extraGraph K colour c).Reachable)
    exact Quot.finite _
  letI : Fintype (extraGraph K colour c).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype (PieceIndex K colour c) :=
    inferInstanceAs (Fintype (Option (extraGraph K colour c).ConnectedComponent))
  have self_contiguous {S : PreAbstractSimplicialComplex (iteratedAmbient D 3).1}
      {a : Vertex S → Vertex C} (ha : Simplicial a) : Contiguous a a := by
    intro s hs
    rw [Finset.union_idempotent]
    exact ha s hs
  have hinc (j : PieceIndex K colour c) : Simplicial (inc j) := by
    have hle : piece j ≤ P := fun _ hs => hs.1
    exact (of_total_simplicial _ _).comp (include_subcomplex_simplicial hle)
  let out := post ∘ select
  have hout : Simplicial out := (of_total_simplicial _ _).comp hselect
  let globalFactor := glue label factor
  let hface := refined_colour_face_in_one_piece f hf colour c
  have chain := glue_contiguity label hface inc (fun j => out ∘ factor j)
    (fun j => self_contiguous (hinc j))
    (fun j => self_contiguous (hout.comp (hfactor j))) hchain
  exact ⟨select, globalFactor, hmember, hselect,
    glue_simplicial label hface factor hfactor, chain⟩

end Pullback

end

end D5.S3.Topology.StableCategory.TetrahedralMainFactorization
