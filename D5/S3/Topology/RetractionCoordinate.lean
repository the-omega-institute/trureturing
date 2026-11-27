/- GID: D5/S3/Topology/RetractionCoordinate
   generality: I
   mirror-B: D5/B/S3/Topology/RetractionCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Interval comparisons glue across faces and extra components retract into single edges. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.OrdinaryTetrahedronCollar
import D5.S3.Topology.IntervalSubdivisionCoordinates
import D5.S3.Topology.OrdinaryCollarRetraction
import D5.S3.Topology.RankColouredTetrahedron
import D5.S3.Topology.RelativeIntervalChartGluing
import D5.S3.Topology.StableCategory.IntervalChartRefinement

/-! The ordinary path coordinates of the colour-collar retraction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace TetrahedronCollar16

open D5.S3.Topology
open D5.S3.Topology.StableCategory
open BarycentricGraphDistance (Face Vertex subdivisionGraph oneSkeleton)
open BarycentricBaseRigidity (vertexOfFace faceImage retainedVertex Contiguous sd subdividedVertex)
open GraphSubdivisionIntervals (originalSupport originalSupport_mem mem_iteratedSubcomplex_iff
  faceImage_singleton)
open PathContiguity (intervalComplex IsIntervalMap)
open RelativeIntervalChartGluing (relative_contiguity_of_interval_charts)
open private simplex_le mem_faceImage_iff iterated_point_face iterated_le_ambient
  from D5.S3.Topology.GraphSubdivisionIntervals
open private toVertexMap contiguous_toVertexMap from D5.S3.Topology.PathContiguity
open D5.S3.Geometry.FiniteAlexanderDualCollapse (simplex)
open IntervalFlagCoordinate (coordinate list_coordinate)
open private asFinset mem_asFinset cut₁ cut₂ subdivisionCoordinate
  from D5.S3.Topology.TetrahedronCollar16
open private flagFinset from D5.S3.Topology.OrdinaryTetrahedronCollar
open private map_face row_eq localVertex from D5.S3.Topology.RankColouredTetrahedron
open private support_mono from D5.S3.Topology.RankColouredTetrahedron
open private image from D5.S3.Topology.OrdinarySubdivisionMap

private theorem list_coordinate_map {A : Type*} [DecidableEq A] (f : A → ℕ) (l : List A) :
    subdivisionCoordinate (l.map f) = coordinate (l.toFinset.image f) := by
  have h : (l.map f).toFinset = l.toFinset.image f := by
    ext n
    simp only [List.mem_toFinset, Finset.mem_image, List.mem_map]
  rw [← h]
  exact list_coordinate (l.map f)

private def faceCoordinate (c : Color) (s : Finset (Fin 4)) : ℕ :=
  coordinate (s.image fun x => x.val - low c)

private def flagCoordinate (c : Color) (s : Finset (Finset (Fin 4))) : ℕ :=
  coordinate (s.image (faceCoordinate c))

private theorem faceCoordinate_asFinset (c : Color) (l : List ℕ)
    (h : ∀ n ∈ l, n < 4) :
    faceCoordinate c (asFinset 4 l) = subdivisionCoordinate (l.map (· - low c)) := by
  rw [list_coordinate_map, faceCoordinate]
  congr 1
  ext n
  simp only [Finset.mem_image, List.mem_toFinset, mem_asFinset]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, h x hx⟩, hx, rfl⟩

private theorem cut₁_bounded (c : Color) (i x : ℕ) (hx : x ∈ cut₁ c i) : x < 4 := by
  have hc := (List.mem_filter.mp hx).2
  simp only [Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with rfl | rfl <;> fin_cases c <;> decide

private theorem cut₂_bounded (c : Color) (i : ℕ) (l : List ℕ) (hl : l ∈ cut₂ c i)
    (x : ℕ) (hx : x ∈ l) : x < 4 := by
  unfold cut₂ at hl
  simp only [List.mem_eraseDups, List.mem_filter, List.mem_map] at hl
  obtain ⟨⟨j, _, rfl⟩, _⟩ := hl
  exact cut₁_bounded c j x hx

private theorem flagCoordinate_flagFinset (c : Color) (l : List (List ℕ))
    (hb : ∀ s ∈ l, ∀ n ∈ s, n < 4) :
    flagCoordinate c (flagFinset l) =
      subdivisionCoordinate (l.map fun s => subdivisionCoordinate (s.map (· - low c))) := by
  rw [flagCoordinate, flagFinset, list_coordinate_map]
  congr 1
  ext n
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, h⟩
    exact ⟨s, hs, (faceCoordinate_asFinset c s (hb s hs)).symm.trans h⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨asFinset 4 s, ⟨s, hs, rfl⟩, (faceCoordinate_asFinset c s (hb s hs)).trans h⟩

open D5.S3.Topology.BarycentricNeighborhoodIteration (iteratedAmbient iteratedSubcomplex)

/-- The retraction height is read from the actual two-cut image flags.
The coordinate of each successive flag is the sum of its extremal old
coordinates. -/
theorem retractionHeight_eq_coordinate (c : Color) (v : V₃) :
    retractionHeight c v =
      coordinate ((OrdinarySubdivisionMap.twoCutImage (hasColour c) (literalFace₃ v)).image
        (flagCoordinate c)) := by
  rw [literalFace₃_retract, retractionHeight, list_coordinate_map]
  congr 1
  ext n
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
  have bounded (s : List (List ℕ)) (hs : s ∈ retract c v) :
      ∀ t ∈ s, ∀ x ∈ t, x < 4 := by
    unfold retract at hs
    simp only [List.mem_eraseDups, List.mem_map] at hs
    obtain ⟨i, _, rfl⟩ := hs
    exact cut₂_bounded c i
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨flagFinset s, ⟨s, hs, rfl⟩, (flagCoordinate_flagFinset c s (bounded s hs)).trans h⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, h⟩
    exact ⟨s, hs, (flagCoordinate_flagFinset c s (bounded s hs)).symm.trans h⟩


noncomputable section

local instance (priority := 2000) (A : Type*) : DecidableEq A := Classical.decEq A

private theorem nat_image_eq {A : Type} (f : A → ℕ) (s : Finset A) :
    @Finset.image A ℕ instDecidableEqNat f s = image s f := by
  ext n
  simp only [image, Finset.mem_image]

private theorem coordinates_after_image {X Y : Type} (f : X → Y) (q : Y → ℕ)
    (s : Finset (Finset (Finset X))) :
    coordinate (@Finset.image _ ℕ instDecidableEqNat
      (fun b : Finset (Finset Y) => coordinate (@Finset.image _ ℕ instDecidableEqNat
        (fun a => coordinate (@Finset.image Y ℕ instDecidableEqNat q a)) b))
      (image s fun b => image b fun a => image a f)) =
      coordinate (s.image fun b => coordinate (b.image fun a => coordinate (a.image (q ∘ f)))) := by
  simp only [nat_image_eq, image, Finset.image_image, Function.comp_def]

private theorem coordinates_of_typed_flag {X : Type} {K : PreAbstractSimplicialComplex X}
    (q : X → ℕ) (v : Face (BarycentricBaseRigidity.sd (BarycentricBaseRigidity.sd K))) :
    coordinate ((v.val.image fun b => b.val.image fun a => a.val).image fun b =>
      coordinate (b.image fun a => coordinate (a.image q))) =
      IntervalSubdivisionCoordinates.iterate (K := K) q 3 v := by
  simp only [Finset.image_image, Function.comp_def]
  rfl

/-- The height computed in the chamber is the ordinary path coordinate
of the actual retracted vertex. The rank colouring can identify vertices. -/
theorem retractionHeight_of_rank_retraction {X : Type} {K : PreAbstractSimplicialComplex X}
    (colour : X → Fin 4) (c : Color) (v : Face (iteratedAmbient K 2).2)
    (hv : InCollar c (RankColouredTetrahedron.row colour v)) :
    retractionHeight c (RankColouredTetrahedron.row colour v) =
      IntervalSubdivisionCoordinates.iterate
        (K := OrdinaryCollarRetraction.colourComplex K (hasColour c ∘ colour))
        (fun x => (colour x).val - low c) 3
        (OrdinaryCollarRetraction.retract (hasColour c ∘ colour)
          ⟨v, (RankColouredTetrahedron.row_inCollar colour c v).mp hv⟩) := by
  let u : {w : Face (iteratedAmbient K 2).2 //
      OrdinarySubdivisionMap.inTwoCutCollar (hasColour c ∘ colour) w} :=
    ⟨v, (RankColouredTetrahedron.row_inCollar colour c v).mp hv⟩
  rw [retractionHeight_eq_coordinate, row_eq]
  unfold localVertex
  rw [OrdinarySubdivisionMap.twoCutImage_iterate colour
    (map_face colour) (hasColour c ∘ colour) (hasColour c)
    (fun _ => rfl)]
  let q : Fin 4 → ℕ := fun x => x.val - low c
  let w := OrdinaryCollarRetraction.retract (hasColour c ∘ colour) u
  let s := OrdinarySubdivisionMap.twoCutImage (hasColour c ∘ colour) v
  let read : Finset (Finset (Finset X)) → ℕ :=
    fun t => coordinate (t.image fun b => coordinate (b.image fun a =>
      coordinate (a.image (q ∘ colour))))
  have himage : (w.val.image fun b => b.val.image fun a => a.val) = s :=
    OrdinaryCollarRetraction.retract_image (hasColour c ∘ colour) u
  calc
    coordinate (@Finset.image _ ℕ instDecidableEqNat (flagCoordinate c)
        (image s fun b => image b fun a => image a colour)) =
        read s := coordinates_after_image colour q s
    _ = read (w.val.image fun b => b.val.image fun a => a.val) :=
      congrArg read himage.symm
    _ = _ := coordinates_of_typed_flag (q ∘ colour) w

/-- A chamber's height picks the actual retracted vertex in any oriented
chart of an old edge containing its selected support. -/
theorem main_retraction_eq_edge_chart {X : Type} {K : PreAbstractSimplicialComplex X}
    (colour : X → Fin 4) (c : Color) (u : Face (iteratedAmbient K 2).2)
    (hu : Main c (RankColouredTetrahedron.row colour u)) :
    let P := OrdinaryCollarRetraction.colourComplex K (hasColour c ∘ colour)
    let q := fun x => (colour x).val - low c
    ∀ (e : Face P) (x : Vertex P)
      (chart : Vertex (intervalComplex 8) → Vertex (iteratedAmbient P 3).2),
      Function.Injective chart →
      (∀ s, s ∈ iteratedSubcomplex P (simplex e.val) 3 ↔
        ∃ (t : Finset ℕ) (ht : t ∈ intervalComplex 8), faceImage chart ht = s) →
      (∀ i : Vertex (intervalComplex 8), i.val = 0 → chart i = retainedVertex 3 x) →
      (∀ s ∈ P, s.image q ∈ intervalComplex 1) →
      Set.InjOn q {x | ({x} : Finset X) ∈ simplex e.val} →
      q x.val = 0 →
      RankColouredTetrahedron.colourSupport colour c u ⊆ e.val →
      ∀ i : Vertex (intervalComplex 8),
        i.val = retractionHeight c (RankColouredTetrahedron.row colour u) →
        chart i = vertexOfFace _ (OrdinaryCollarRetraction.retract (hasColour c ∘ colour)
          ⟨u, (RankColouredTetrahedron.row_inCollar colour c u).mp (main_conditions hu).1⟩) := by
  intro P q e x chart hinj hfaces hstart hq hqinj hx hs i hi
  let hu' := (RankColouredTetrahedron.row_inCollar colour c u).mp (main_conditions hu).1
  let w := OrdinaryCollarRetraction.retract (hasColour c ∘ colour) ⟨u, hu'⟩
  let v : Vertex (iteratedAmbient P 3).2 := vertexOfFace _ w
  have hw := OrdinaryCollarRetraction.retract_support (hasColour c ∘ colour) ⟨u, hu'⟩
  have hmem : ({v.val} : Finset _) ∈ iteratedSubcomplex P (simplex e.val) 3 := by
    apply (mem_iteratedSubcomplex_iff (B := simplex e.val) 3 v.property).2
    change originalSupport P 3 {w} = RankColouredTetrahedron.colourSupport colour c u at hw
    change originalSupport P 3 {w} ∈ simplex e.val
    have hP : originalSupport P 3 {w} ∈ P := originalSupport_mem 3 v.property
    rw [hw] at hP ⊢
    have hne := (P.isRelLowerSet_faces hP).1
    exact ⟨hne, hs⟩
  obtain ⟨t, ht, heq⟩ := (hfaces _).mp hmem
  have hpre : v.val ∈ faceImage chart ht := heq.symm ▸ Finset.mem_singleton_self _
  obtain ⟨j, _, hj⟩ := (mem_faceImage_iff chart ht v.val).mp hpre
  have hjv : chart j = v := Subtype.ext hj
  have hidx := IntervalSubdivisionCoordinates.iterate_eq_chart_index (simplex_le e.property)
    q hq hqinj 3 chart hinj (fun t ht => (hfaces _).mpr ⟨t, ht, rfl⟩) x hx hstart j
  rw [hjv] at hidx
  have heval := retractionHeight_of_rank_retraction colour c u (main_conditions hu).1
  change retractionHeight c (RankColouredTetrahedron.row colour u) =
    IntervalSubdivisionCoordinates.iterate (K := P) q 3 v.val at heval
  have hij : i = j := Subtype.ext (hi.trans (heval.trans hidx))
  exact (congrArg chart hij).trans hjv

private theorem old_path_coordinate {X : Type} {K : PreAbstractSimplicialComplex X}
    (colour : X → Fin 4) (c : Color)
    (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X)) :
    let P := OrdinaryCollarRetraction.colourComplex K (hasColour c ∘ colour)
    let q := fun x => (colour x).val - low c
    (∀ s ∈ P, s.image q ∈ intervalComplex 1) ∧
    (∀ s ∈ P, Set.InjOn q (s : Set X)) := by
  intro P q
  have hrank (a : Fin 4) (h : hasColour c a = true) :
      a.val - low c ≤ 1 ∧ a.val = low c + (a.val - low c) := by
    simp only [hasColour, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · rw [h, Nat.sub_self, Nat.add_zero]
      exact ⟨Nat.zero_le _, rfl⟩
    · rw [h, high, Nat.add_sub_cancel_left]
      exact ⟨le_rfl, rfl⟩
  constructor
  · intro s hs
    have hq (n : ℕ) (hn : n ∈ s.image q) : n ≤ 1 := by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
      exact (hrank (colour x) (hs.2 _ hx)).1
    refine ⟨((P.isRelLowerSet_faces hs).1.image _), hq, ?_⟩
    intro a ha b _
    exact (hq a ha).trans (Nat.succ_le_succ (Nat.zero_le b))
  · intro s hs x hx y hy h
    apply hinj s hs.1 hx hy
    apply Fin.ext
    exact (hrank (colour x) (hs.2 x hx)).2.trans
      ((congrArg (low c + ·) h).trans (hrank (colour y) (hs.2 y hy)).2.symm)

private theorem oriented_colour_edges {X : Type} {K : PreAbstractSimplicialComplex X}
    (colour : X → Fin 4) (c : Color)
    (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X)) :
    let P := OrdinaryCollarRetraction.colourComplex K (hasColour c ∘ colour)
    let q := fun x => (colour x).val - low c
    let E := {e : Face P // e.val.val.card = 2}
    (∀ s ∈ P, (s : Finset X).card ≤ 2) ∧
    ∃ left right : E → Vertex P, ∀ e,
      e.val.val = {(left e).val, (right e).val} ∧
      left e ≠ right e ∧ q (left e).val = 0 ∧ q (right e).val = 1 := by
  intro P q E
  have hq := old_path_coordinate (K := K) colour c hinj
  have hsubset (s : Finset X) (hs : s ∈ P) : s.image q ⊆ {0, 1} := by
    intro a ha
    have hle := (hq.1 s hs).2.1 a ha
    have h : a = 0 ∨ a = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hle
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have h01 : ({0, 1} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  constructor
  · intro s hs
    rw [← Finset.card_image_of_injOn (hq.2 s hs), ← h01]
    exact Finset.card_le_card (hsubset s hs)
  have edge (e : E) : ∃ x y : Vertex P,
      e.val.val = {x.val, y.val} ∧ x ≠ y ∧ q x.val = 0 ∧ q y.val = 1 := by
    let s := e.val.val
    have hs : s ∈ P := e.val.property
    have hc : (s.image q).card = 2 :=
      (Finset.card_image_of_injOn (hq.2 s hs)).trans e.property
    have hpair : s.image q = {0, 1} :=
      Finset.eq_of_subset_of_card_le (hsubset s hs) (h01.trans hc.symm).le
    have exists_at (a : ℕ) (ha : a ∈ ({0, 1} : Finset ℕ)) : ∃ x ∈ s, q x = a :=
      Finset.mem_image.mp (hpair.symm ▸ ha)
    obtain ⟨x, hx, hxq⟩ := exists_at 0 (Finset.mem_insert_self _ _)
    obtain ⟨y, hy, hyq⟩ := exists_at 1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hn : x ≠ y := fun e => Nat.zero_ne_one (hxq.symm.trans ((congrArg q e).trans hyq))
    let L : Vertex P := ⟨x, (P.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hx)
      (Finset.singleton_nonempty _)⟩
    let R : Vertex P := ⟨y, (P.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hy)
      (Finset.singleton_nonempty _)⟩
    refine ⟨L, R, ?_, fun h => hn (congrArg Subtype.val h), hxq, hyq⟩
    symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩
    · rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hn),
        Finset.card_singleton]
      exact e.property.le
  choose left right h using edge
  exact ⟨left, right, h⟩

/-- At a thin face, the retraction and both interval heights are pinned
to its unique selected old vertex. -/
theorem main_retraction_at_singleton {X : Type} {K : PreAbstractSimplicialComplex X}
    (colour : X → Fin 4) (c : Color) (u : Face (iteratedAmbient K 2).2)
    (hu : Main c (RankColouredTetrahedron.row colour u))
    (x : Vertex (OrdinaryCollarRetraction.colourComplex K (hasColour c ∘ colour)))
    (hx : RankColouredTetrahedron.colourSupport colour c u = {x.val}) :
    let a := RankColouredTetrahedron.row colour u
    let n := (colour x.val).val - low c
    retractionHeight c a = 8 * n ∧ height a = 16 * n ∧
      IsEndpoint c (colour x.val).val a ∧
      vertexOfFace _ (OrdinaryCollarRetraction.retract (hasColour c ∘ colour)
        ⟨u, (RankColouredTetrahedron.row_inCollar colour c u).mp (main_conditions hu).1⟩)
        = retainedVertex 3 x := by
  intro a n
  have hb (d : Color) : low d < 4 ∧ high d < 4 := by fin_cases d <;> decide
  have witness (j : ℕ) (hj : j = low c ∨ j = high c) (hm : j ∈ carrier a) :
      (colour x.val).val = j := by
    have hj' : j < 4 := hj.elim (fun h => h.symm ▸ (hb c).1) (fun h => h.symm ▸ (hb c).2)
    obtain ⟨y, hy, hcol⟩ := (RankColouredTetrahedron.mem_carrier_row colour u ⟨j, hj'⟩).mp hm
    have hyC : y ∈ RankColouredTetrahedron.colourSupport colour c u := by
      apply Finset.mem_filter.mpr
      refine ⟨hy, ?_⟩
      simp only [hasColour, Bool.or_eq_true, beq_iff_eq]
      simpa only [hcol] using hj
    rw [hx, Finset.mem_singleton] at hyC
    exact hyC ▸ congrArg Fin.val hcol
  have hboundary : OnBoundary c a := by
    rintro ⟨hl, hr⟩
    have hl' := witness _ (Or.inl rfl) hl
    have hr' := witness _ (Or.inr rfl) hr
    exact Nat.ne_of_lt (Nat.lt_succ_self (low c)) (hl'.symm.trans hr')
  have hpin := thin_face_pin c a hu hboundary
  have hn : retractionHeight c a = 8 * n ∧ height a = 16 * n ∧
      IsEndpoint c (colour x.val).val a := by
    rcases hpin with ⟨hl, hr, hh⟩ | ⟨hl, hr, hh⟩
    · have hc := witness _ (Or.inl rfl) hl
      have hn0 : n = 0 := by dsimp [n]; rw [hc, Nat.sub_self]
      rw [hn0, hc]
      exact ⟨(retraction_position hu).2.1.mp hr, hh, hr⟩
    · have hc := witness _ (Or.inr rfl) hl
      have hn1 : n = 1 := by dsimp [n]; rw [hc, high, Nat.add_sub_cancel_left]
      rw [hn1, hc]
      exact ⟨(retraction_position hu).2.2.mp hr, hh, hr⟩
  refine ⟨hn.1, hn.2.1, hn.2.2, ?_⟩
  let P := OrdinaryCollarRetraction.colourComplex K (hasColour c ∘ colour)
  let hu' := (RankColouredTetrahedron.row_inCollar colour c u).mp (main_conditions hu).1
  let w := OrdinaryCollarRetraction.retract (hasColour c ∘ colour) ⟨u, hu'⟩
  let v : Vertex (iteratedAmbient P 3).2 := vertexOfFace _ w
  have hw := OrdinaryCollarRetraction.retract_support (hasColour c ∘ colour) ⟨u, hu'⟩
  change originalSupport P 3 {w} = RankColouredTetrahedron.colourSupport colour c u at hw
  have hmem : ({v.val} : Finset _) ∈ iteratedSubcomplex P (simplex {x.val}) 3 := by
    apply (mem_iteratedSubcomplex_iff (B := simplex {x.val}) 3 v.property).2
    change originalSupport P 3 {w} ∈ simplex {x.val}
    rw [hw, hx]
    exact ⟨Finset.singleton_nonempty _, Finset.Subset.rfl⟩
  change v = retainedVertex 3 x
  exact Subtype.ext (Finset.singleton_injective (iterated_point_face 3 x hmem))

/-- The full subcomplex spanned by the main vertices of a given colour. -/
def mainComplex {X : Type} (K : PreAbstractSimplicialComplex X)
    (colour : X → Fin 4) (c : Color) :
    PreAbstractSimplicialComplex (iteratedAmbient K 3).1 :=
  OrdinaryCollarRetraction.colourComplex (iteratedAmbient K 3).2 fun u =>
    decide (Main c (RankColouredTetrahedron.row colour u))

private theorem main_of_vertex {X : Type} {K : PreAbstractSimplicialComplex X}
    {colour : X → Fin 4} {c : Color} (u : Vertex (mainComplex K colour c)) :
    Main c (RankColouredTetrahedron.row colour u.val) :=
  of_decide_eq_true (u.property.2 _ (Finset.mem_singleton_self _))

private def intervalPoint {N : ℕ} (n : ℕ) (h : n ≤ N) : Vertex (intervalComplex N) :=
  ⟨n, Finset.singleton_nonempty _, fun _ ha => (Finset.mem_singleton.mp ha).symm ▸ h,
    fun _ ha _ hb => by
      rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
      exact Nat.le_succ _⟩

private theorem main_retraction_charts {X : Type} {K : PreAbstractSimplicialComplex X}
    [Finite (iteratedAmbient K 3).1]
    (colour : X → Fin 4) (c : Color)
    (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X)) :
    let A := OrdinaryCollarRetraction.colourComplex K (hasColour c ∘ colour)
    let P := mainComplex K colour c
    let E := {e : Face A // e.val.val.card = 2}
    let q := fun x => (colour x).val - low c
    ∃ (chart : E → Vertex (intervalComplex 8) → Vertex (iteratedAmbient A 3).2)
      (g : Vertex P → Vertex (iteratedAmbient A 3).2),
      (∀ e s (hs : s ∈ intervalComplex 8),
        faceImage (chart e) hs ∈ iteratedSubcomplex A (simplex e.val.val) 3) ∧
      (∀ u (e : E), RankColouredTetrahedron.colourSupport colour c u.val = e.val.val →
        ∃ i, i.val = height (RankColouredTetrahedron.row colour u.val) / 2 ∧ g u = chart e i) ∧
      (∀ e, Function.Injective (chart e)) ∧
      (∀ e i, IntervalSubdivisionCoordinates.iterate (K := A) q 3 (chart e i).val = i.val) ∧
      (∀ e (x : Vertex A) i, x.val ∈ e.val.val → i.val = 8 * q x.val →
        chart e i = retainedVertex 3 x) ∧
      (∀ u (x : Vertex A), RankColouredTetrahedron.colourSupport colour c u.val = {x.val} →
        g u = retainedVertex 3 x) ∧
      (∀ s ∈ P, ((originalSupport K 3 s).filter fun x => (hasColour c ∘ colour) x = true) ∈ A) ∧
      IsIntervalMap (oneSkeleton P) 16 (fun u => height (RankColouredTetrahedron.row colour u.val)) ∧
      Relation.ReflTransGen Contiguous
        (fun u : Vertex P => vertexOfFace _ (OrdinaryCollarRetraction.retract
          (hasColour c ∘ colour) ⟨u.val, (RankColouredTetrahedron.row_inCollar colour c u.val).mp
            (main_conditions (main_of_vertex u)).1⟩)) g := by
  intro A P E q
  obtain ⟨hdim, left, right, horient⟩ := oriented_colour_edges (K := K) colour c hinj
  obtain ⟨chart, hinjChart, hend, hfaces, _, _⟩ := GraphSubdivisionIntervals.graph_subdivision_intervals_oriented
    A hdim 3 left right (fun e => ⟨(horient e).1, (horient e).2.1⟩)
  have hchart (e : E) (s : Finset ℕ) (hs : s ∈ intervalComplex 8) :
      faceImage (chart e) hs ∈ iteratedSubcomplex A (simplex e.val.val) 3 :=
    (hfaces e _).mpr ⟨s, hs, rfl⟩
  have hq := old_path_coordinate (K := K) colour c hinj
  have hqinj (e : E) : Set.InjOn q {x | ({x} : Finset X) ∈ simplex e.val.val} := by
    apply (hq.2 _ e.val.property).mono
    intro x hx
    exact hx.2 (Finset.mem_singleton_self _)
  have hindex (e : E) (i : Vertex (intervalComplex 8)) :
      IntervalSubdivisionCoordinates.iterate (K := A) q 3 (chart e i).val = i.val :=
    IntervalSubdivisionCoordinates.iterate_eq_chart_index (simplex_le e.val.property) q
      hq.1 (hqinj e) 3 (chart e) (hinjChart e) (hchart e) (left e)
      (horient e).2.2.1 (fun j hj => (hend e j).1 hj) i
  have hendpoint (e : E) (x : Vertex A) (i : Vertex (intervalComplex 8))
      (hx : x.val ∈ e.val.val) (hi : i.val = 8 * q x.val) : chart e i = retainedVertex 3 x := by
    rw [(horient e).1, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · have hx' : x = left e := Subtype.ext hx
      have hq0 : q (left e).val = 0 := (horient e).2.2.1
      rw [hx', hq0, Nat.mul_zero] at hi
      exact ((hend e i).1 hi).trans (congrArg (retainedVertex 3) hx'.symm)
    · have hx' : x = right e := Subtype.ext hx
      have hq1 : q (right e).val = 1 := (horient e).2.2.2
      rw [hx', hq1, Nat.mul_one] at hi
      exact ((hend e i).2 hi).trans (congrArg (retainedVertex 3) hx'.symm)
  let sel := hasColour c ∘ colour
  let support (s : Finset (iteratedAmbient K 3).1) :=
    (originalSupport K 3 s).filter fun x => sel x = true
  let small (u : Vertex P) := RankColouredTetrahedron.colourSupport colour c u.val
  let row (u : Vertex P) : onMain c := ⟨RankColouredTetrahedron.row colour u.val, main_of_vertex u⟩
  let r (u : Vertex P) : Vertex (iteratedAmbient A 3).2 :=
    vertexOfFace _ (OrdinaryCollarRetraction.retract sel
      ⟨u.val, (RankColouredTetrahedron.row_inCollar colour c u.val).mp (main_conditions (row u).property).1⟩)
  have hsmall (u : Vertex P) : small u ∈ A := by
    have hr := OrdinaryCollarRetraction.retract_support sel
      ⟨u.val, (RankColouredTetrahedron.row_inCollar colour c u.val).mp (main_conditions (row u).property).1⟩
    change originalSupport A 3 {(r u).val} = small u at hr
    rw [← hr]
    exact originalSupport_mem 3 (r u).property
  have hsubset (s : Finset (iteratedAmbient K 3).1) (u : Vertex P) (hu : u.val ∈ s) :
      small u ⊆ support s :=
    Finset.filter_subset_filter _ (support_mono 3 (Finset.singleton_subset_iff.mpr hu))
  have hsupport (s : Finset (iteratedAmbient K 3).1) (hs : s ∈ P) : support s ∈ A := by
    obtain ⟨u, hu⟩ := (P.isRelLowerSet_faces hs).1
    let v : Vertex P := ⟨u, (P.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hu)
      (Finset.singleton_nonempty _)⟩
    have hsK : s ∈ (iteratedAmbient K 3).2 := hs.1
    have hS := originalSupport_mem 3 hsK
    exact ⟨(K.isRelLowerSet_faces hS).2 (Finset.filter_subset _ _)
      (((A.isRelLowerSet_faces (hsmall v)).1).mono (hsubset s v hu)),
      fun x hx => (Finset.mem_filter.mp hx).2⟩
  have cases_support (s : Finset X) (hs : s ∈ A) :
      (∃ x : Vertex A, s = {x.val}) ∨ ∃ e : E, s = e.val.val := by
    by_cases htwo : s.card = 2
    · exact Or.inr ⟨⟨⟨s, hs⟩, htwo⟩, rfl⟩
    · have hpos := Finset.card_pos.mpr (A.isRelLowerSet_faces hs).1
      have hle := hdim s hs
      have hone : s.card = 1 :=
        Nat.le_antisymm (Nat.le_of_lt_succ (lt_of_le_of_ne hle htwo)) hpos
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
      exact Or.inl ⟨⟨x, hx ▸ hs⟩, hx⟩
  have hchoice (u : Vertex P) : ∃ place : Vertex (intervalComplex 8) → Vertex (iteratedAmbient A 3).2,
      (∀ x : Vertex A, small u = {x.val} → ∀ i, place i = retainedVertex 3 x) ∧
      (∀ e : E, small u = e.val.val → place = chart e) := by
    rcases cases_support _ (hsmall u) with ⟨x, hx⟩ | ⟨e, he⟩
    · refine ⟨fun _ => retainedVertex 3 x, ?_, ?_⟩
      · intro y hy i
        have hxy := Finset.singleton_injective (hx.symm.trans hy)
        exact congrArg (retainedVertex 3) (Subtype.ext hxy)
      · intro e he
        have hc := congrArg Finset.card (he.symm.trans hx)
        have hcard : e.val.val.card = 2 := e.property
        change e.val.val.card = ({x.val} : Finset X).card at hc
        rw [hcard, Finset.card_singleton] at hc
        exact (Nat.ne_of_gt (Nat.lt_succ_self 1) hc).elim
    · refine ⟨chart e, ?_, ?_⟩
      · intro x hx i
        have hc := congrArg Finset.card (he.symm.trans hx)
        have hcard : e.val.val.card = 2 := e.property
        change e.val.val.card = ({x.val} : Finset X).card at hc
        rw [hcard, Finset.card_singleton] at hc
        exact (Nat.ne_of_gt (Nat.lt_succ_self 1) hc).elim
      · intro d hd
        have hed : e = d := Subtype.ext (Subtype.ext (he.symm.trans hd))
        exact congrArg chart hed
  choose place hpoint hedge using hchoice
  have hrow (u v : Vertex P) (h : (oneSkeleton P).Adj u v) :
      row u = row v ∨ (graph.induce (onMain c)).Adj (row u) (row v) := by
    have hpair : ({u.val, v.val} : Finset _) ∈ (iteratedAmbient K 3).2 := h.2.1
    have hne : u.val ≠ v.val := fun e => h.1 (Subtype.ext e)
    have ha : (subdivisionGraph (iteratedAmbient K 2).2).Adj u.val v.val :=
      hpair.2.1 (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hne
    exact (RankColouredTetrahedron.row_eq_or_adj colour ha).imp Subtype.ext id
  have pull {N : ℕ} (a : onMain c → ℕ)
      (ha : IsIntervalMap (graph.induce (onMain c)) N a) :
      IsIntervalMap (oneSkeleton P) N (a ∘ row) := by
    refine ⟨fun u => ha.1 (row u), ?_⟩
    intro u v h
    rcases hrow u v h with he | he
    · simp only [Function.comp_apply, he, Nat.le_succ, and_self]
    · exact ha.2 he
  have hr := pull _ (retraction_interval c)
  have hh := pull _ (main_interval c)
  let f (u : Vertex P) := intervalPoint (retractionHeight c (row u).val) (hr.1 u)
  let g (u : Vertex P) := intervalPoint (height (row u).val / 2)
    (show height (row u).val / 2 ≤ 8 from Nat.div_le_of_le_mul (hh.1 u))
  have hg : IsIntervalMap (oneSkeleton P) 8 (fun u => (g u).val) := by
    refine ⟨fun u => (g u).property.2.1 _ (Finset.mem_singleton_self _), ?_⟩
    intro u v h
    obtain ⟨hu, hv⟩ := hh.2 h
    change height (row u).val ≤ height (row v).val + 1 at hu
    change height (row v).val ≤ height (row u).val + 1 at hv
    change height (row u).val / 2 ≤ height (row v).val / 2 + 1 ∧
      height (row v).val / 2 ≤ height (row u).val / 2 + 1
    have halve {a b : ℕ} (h : a ≤ b + 1) : a / 2 ≤ b / 2 + 1 := by
      have hle : a ≤ b + 2 * 1 := h.trans (Nat.add_le_add_left (by decide) b)
      exact (Nat.div_le_div_right hle).trans_eq (Nat.add_mul_div_left b 1 (by decide))
    exact ⟨halve hu, halve hv⟩
  let S : Set (Vertex P) := {u | ∃ x : Vertex A, small u = {x.val}}
  have hfix : Set.EqOn f g S := by
    rintro u ⟨x, hx⟩
    obtain ⟨hrp, hhp, _, _⟩ := main_retraction_at_singleton colour c u.val (row u).property x hx
    apply Subtype.ext
    change retractionHeight c (row u).val = height (row u).val / 2
    rw [hrp, hhp, show 16 = 8 * 2 from rfl, Nat.mul_right_comm, Nat.mul_div_cancel _ (by decide : 0 < 2)]
  have hconstant (x : Vertex A) (t : Finset ℕ) (ht : t ∈ intervalComplex 8) :
      faceImage (fun _ => retainedVertex 3 x) ht ∈ (iteratedAmbient A 3).2 := by
    have eq : faceImage (fun _ => retainedVertex 3 x) ht = {(retainedVertex 3 x).val} :=
      Finset.image_const ht.1.attach _
    rw [eq]
    exact (retainedVertex 3 x).property
  have hface (s : Finset _) (hs : s ∈ P) :
      ∃ e : Vertex (intervalComplex 8) → Vertex (iteratedAmbient A 3).2,
        (∀ t (ht : t ∈ intervalComplex 8), faceImage e ht ∈ (iteratedAmbient A 3).2) ∧
        ∀ u : Vertex P, u.val ∈ s → ∀ i, (u ∈ S → i = f u) → place u i = e i := by
    rcases cases_support _ (hsupport s hs) with ⟨x, hx⟩ | ⟨e, he⟩
    · refine ⟨fun _ => retainedVertex 3 x, hconstant x, ?_⟩
      intro u hu i _
      have hsub : small u ⊆ {x.val} := hx ▸ hsubset s u hu
      have hcard : ({x.val} : Finset X).card ≤ (small u).card := by
        rw [Finset.card_singleton]
        exact Finset.card_pos.mpr (A.isRelLowerSet_faces (hsmall u)).1
      exact hpoint u x (Finset.eq_of_subset_of_card_le hsub hcard) i
    · refine ⟨chart e, fun t ht => iterated_le_ambient (simplex_le e.val.property) 3 (hchart e t ht), ?_⟩
      intro u hu i hi
      have hsub : small u ⊆ e.val.val := he ▸ hsubset s u hu
      rcases cases_support _ (hsmall u) with ⟨x, hx⟩ | ⟨d, hd⟩
      · rw [hpoint u x hx, hi ⟨x, hx⟩]
        have hxe : x.val ∈ e.val.val := hsub (hx.symm ▸ Finset.mem_singleton_self _)
        rw [(horient e).1, Finset.mem_insert, Finset.mem_singleton] at hxe
        obtain ⟨hcoord, _, _, _⟩ := main_retraction_at_singleton colour c u.val (row u).property x hx
        rcases hxe with hx' | hx'
        · have hzero : (f u).val = 0 := by
            change retractionHeight c (row u).val = 0
            have hleft : (colour (left e).val).val - low c = 0 := (horient e).2.2.1
            rw [hcoord, hx', hleft, Nat.mul_zero]
          exact (congrArg (retainedVertex 3) (Subtype.ext hx')).trans ((hend e (f u)).1 hzero).symm
        · have hone : (f u).val = 8 := by
            change retractionHeight c (row u).val = 8
            have hright : (colour (right e).val).val - low c = 1 := (horient e).2.2.2
            rw [hcoord, hx', hright, Nat.mul_one]
          exact (congrArg (retainedVertex 3) (Subtype.ext hx')).trans ((hend e (f u)).2 hone).symm
      · have heq : small u = e.val.val :=
          Finset.eq_of_subset_of_card_le hsub (e.property.trans (hd ▸ d.property).symm).le
        rw [hedge u e heq]
  have hstart (u : Vertex P) : place u (f u) = r u := by
    rcases cases_support _ (hsmall u) with ⟨x, hx⟩ | ⟨e, he⟩
    · rw [hpoint u x hx]
      exact (main_retraction_at_singleton colour c u.val (row u).property x hx).2.2.2.symm
    · rw [hedge u e he]
      exact main_retraction_eq_edge_chart colour c u.val (row u).property e.val (left e) (chart e)
        (hinjChart e) (hfaces e) (fun i hi => (hend e i).1 hi) hq.1 (hqinj e)
        (horient e).2.2.1 he.le (f u) rfl
  refine ⟨chart, fun u => place u (g u), hchart, ?_, hinjChart, hindex, hendpoint, ?_,
    hsupport, hh, ?_⟩
  · intro u e he
    exact ⟨g u, rfl, congrFun (hedge u e he) (g u)⟩
  · exact fun u x hx => hpoint u x hx (g u)
  · have hc := relative_contiguity_of_interval_charts 8 S f g hr hg hfix place hface
    have he : (fun u => place u (f u)) = r := funext hstart
    rw [he] at hc
    exact (Relation.ReflTransGen.mono
      (r := fun a b => Contiguous a b ∧ Set.EqOn a r S ∧ Set.EqOn b r S)
      (p := Contiguous) (fun _ _ h => h.1)) _ _ hc

/-- Relative interpolation on the tetrahedral heights glues on an
arbitrary properly rank-coloured complex. Along a thin face, it fixes the
image of the unique selected old vertex. -/
theorem main_retraction_glued {X : Type} {K : PreAbstractSimplicialComplex X}
    [Finite (iteratedAmbient K 3).1]
    (colour : X → Fin 4) (c : Color)
    (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X)) :
    let A := OrdinaryCollarRetraction.colourComplex K (hasColour c ∘ colour)
    let P := mainComplex K colour c
    let E := {e : Face A // e.val.val.card = 2}
    ∃ (chart : E → Vertex (intervalComplex 8) → Vertex (iteratedAmbient A 3).2)
      (g : Vertex P → Vertex (iteratedAmbient A 3).2),
      (∀ e s (hs : s ∈ intervalComplex 8),
        faceImage (chart e) hs ∈ iteratedSubcomplex A (simplex e.val.val) 3) ∧
      (∀ u (e : E), RankColouredTetrahedron.colourSupport colour c u.val = e.val.val →
        ∃ i, i.val = height (RankColouredTetrahedron.row colour u.val) / 2 ∧ g u = chart e i) ∧
      Relation.ReflTransGen Contiguous
        (fun u : Vertex P => vertexOfFace _ (OrdinaryCollarRetraction.retract
          (hasColour c ∘ colour) ⟨u.val, (RankColouredTetrahedron.row_inCollar colour c u.val).mp
            (main_conditions (main_of_vertex u)).1⟩)) g := by
  obtain ⟨chart, g, hfaces, hheight, _, _, _, _, _, _, hc⟩ := main_retraction_charts colour c hinj
  exact ⟨chart, g, hfaces, hheight, hc⟩

/-- The main region refines its selected graph by one subdivision.
Projecting each refined face to its lower coordinate gives a map in the
contiguity class of the actual two-cut retraction. -/
theorem main_retraction_glued_refined {X : Type} {K : PreAbstractSimplicialComplex X}
    [Finite (iteratedAmbient K 3).1]
    (colour : X → Fin 4) (c : Color)
    (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X)) :
    let A := OrdinaryCollarRetraction.colourComplex K (hasColour c ∘ colour)
    let B := (iteratedAmbient A 3).2
    let P := mainComplex K colour c
    ∃ (select : Vertex (sd B) → Vertex B) (lift : Vertex P → Vertex (sd B)),
      (∀ v, (select v).val ∈ v.val.val) ∧
      (∀ s (hs : s ∈ sd B), faceImage select hs ∈ B) ∧
      (∀ s (hs : s ∈ P), faceImage lift hs ∈ sd B) ∧
      Relation.ReflTransGen Contiguous
        (fun u : Vertex P => vertexOfFace _ (OrdinaryCollarRetraction.retract
          (hasColour c ∘ colour) ⟨u.val, (RankColouredTetrahedron.row_inCollar colour c u.val).mp
            (main_conditions (main_of_vertex u)).1⟩)) (select ∘ lift) := by
  intro A B P
  let E := {e : Face A // e.val.val.card = 2}
  let q : X → ℕ := fun x => (colour x).val - low c
  let old := IntervalSubdivisionCoordinates.iterate (K := A) q 3
  let small (u : Vertex P) := RankColouredTetrahedron.colourSupport colour c u.val
  let support (s : Finset (iteratedAmbient K 3).1) :=
    (originalSupport K 3 s).filter fun x => (hasColour c ∘ colour) x = true
  obtain ⟨chart, g, hchart, hhalf, hinjChart, hindex, hendpoint, hgpoint, hsupport, hh, hc⟩ :=
    main_retraction_charts colour c hinj
  have edge_refinement (e : E) :=
    IntervalChartRefinement.refined_chart_floor (chart e) (hinjChart e)
      (fun s hs => iterated_le_ambient (simplex_le e.val.property) 3 (hchart e s hs))
  choose fine hfine hparent heven using edge_refinement
  obtain ⟨select, hselect, hselectFace⟩ :=
    IntervalChartRefinement.exists_coordinate_minimum_selector B old
  let h (u : Vertex P) := height (RankColouredTetrahedron.row colour u.val)
  let pos : Vertex P → Vertex (intervalComplex 16) := toVertexMap 16 h
  have hpos (u : Vertex P) : (pos u).val = h u := min_eq_left (hh.1 u)
  have hposFace (s : Finset _) (hs : s ∈ P) : faceImage pos hs ∈ intervalComplex 16 := by
    have hnum : PathContiguity.Contiguous (oneSkeleton P) h h := by
      intro u v huv
      rw [max_self, min_self]
      rcases huv with he | he
      · rw [he]
        exact Nat.le_succ _
      · exact (hh.2 he).1
    simpa only [Finset.union_self] using (contiguous_toVertexMap hh.1 hh.1 hnum) s hs
  have hdim := (oriented_colour_edges (K := K) colour c hinj).1
  have cases_support (s : Finset X) (hs : s ∈ A) :
      (∃ x : Vertex A, s = {x.val}) ∨ ∃ e : E, s = e.val.val := by
    by_cases htwo : s.card = 2
    · exact Or.inr ⟨⟨⟨s, hs⟩, htwo⟩, rfl⟩
    · have hp := Finset.card_pos.mpr (A.isRelLowerSet_faces hs).1
      have he : s.card = 1 :=
        Nat.le_antisymm (Nat.le_of_lt_succ (lt_of_le_of_ne (hdim s hs) htwo)) hp
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp he
      exact Or.inl ⟨⟨x, hx ▸ hs⟩, hx⟩
  have hsmall (u : Vertex P) : small u ∈ A := hsupport _ u.property
  have no_pair (x : Vertex A) (e : E) : e.val.val ≠ ({x.val} : Finset X) := by
    intro he
    have hc : (2 : ℕ) = 1 := e.property.symm.trans
      ((congrArg Finset.card he).trans (Finset.card_singleton _))
    exact Nat.ne_of_gt (Nat.lt_succ_self 1) hc
  let retained (x : Vertex A) : Vertex (sd B) := subdividedVertex (retainedVertex 3 x)
  have choices (u : Vertex P) : ∃ w : Vertex (sd B),
      (∀ x : Vertex A, small u = {x.val} → w = retained x) ∧
      (∀ e : E, small u = e.val.val → w = fine e (pos u)) := by
    rcases cases_support _ (hsmall u) with ⟨x, hx⟩ | ⟨e, he⟩
    · refine ⟨retained x, ?_, fun e he => (no_pair x e (he.symm.trans hx)).elim⟩
      intro y hy
      exact congrArg retained (Subtype.ext (Finset.singleton_injective (hx.symm.trans hy)))
    · refine ⟨fine e (pos u), fun x hx => (no_pair x e (he.symm.trans hx)).elim, ?_⟩
      intro e' he'
      have eq : e = e' := Subtype.ext (Subtype.ext (he.symm.trans he'))
      rw [eq]
  choose lift hliftPoint hliftEdge using choices
  have hsimp (s : Finset _) (hs : s ∈ P) : faceImage lift hs ∈ sd B := by
    have hsub (u : Vertex P) (hu : u.val ∈ s) : small u ⊆ support s :=
      Finset.filter_subset_filter _ (support_mono 3 (Finset.singleton_subset_iff.mpr hu))
    have nonempty : (faceImage lift hs).Nonempty := (P.isRelLowerSet_faces hs).1.attach.image _
    rcases cases_support _ (hsupport s hs) with ⟨x, hx⟩ | ⟨e, he⟩
    · apply ((sd B).isRelLowerSet_faces (retained x).property).2 _ nonempty
      intro y hy
      obtain ⟨u, hu, rfl⟩ := (mem_faceImage_iff lift hs y).mp hy
      have hs' : small u ⊆ {x.val} := hx ▸ hsub u hu
      have hcard : ({x.val} : Finset X).card ≤ (small u).card := by
        rw [Finset.card_singleton]
        exact Finset.card_pos.mpr (A.isRelLowerSet_faces (hsmall u)).1
      rw [hliftPoint u x (Finset.eq_of_subset_of_card_le hs' hcard)]
      exact Finset.mem_singleton_self _
    · apply ((sd B).isRelLowerSet_faces (hfine e _ (hposFace s hs))).2 _ nonempty
      intro y hy
      obtain ⟨u, hu, huy⟩ := (mem_faceImage_iff lift hs y).mp hy
      have hs' : small u ⊆ e.val.val := he ▸ hsub u hu
      have hplace : lift u = fine e (pos u) := by
        rcases cases_support _ (hsmall u) with ⟨x, hx⟩ | ⟨e', he'⟩
        · rw [hliftPoint u x hx]
          have hx' : x.val ∈ e.val.val := hs' (hx.symm ▸ Finset.mem_singleton_self _)
          obtain ⟨_, hh', _, _⟩ :=
            main_retraction_at_singleton colour c u.val (main_of_vertex u) x hx
          have hq : q x.val ≤ 1 := by
            have hq := (old_path_coordinate (K := K) colour c hinj).1 {x.val} x.property
            exact hq.2.1 _ (Finset.mem_image.mpr ⟨_, Finset.mem_singleton_self _, rfl⟩)
          let i := intervalPoint (8 * q x.val)
            (show 8 * q x.val ≤ 8 from (Nat.mul_le_mul_left 8 hq).trans_eq (Nat.mul_one 8))
          have hpos' : (pos u).val = 2 * i.val := by
            have hh'' : h u = 16 * q x.val := hh'
            rw [hpos, hh'']
            change 16 * q x.val = 2 * (8 * q x.val)
            exact Nat.mul_assoc 2 8 _
          rw [heven e (pos u) i hpos', hendpoint e x i hx' rfl]
        · have heq : small u = e.val.val :=
            Finset.eq_of_subset_of_card_le hs' (e.property.trans (he' ▸ e'.property).symm).le
          exact hliftEdge u e heq
      apply (mem_faceImage_iff (fine e) (hposFace s hs) y).mpr
      refine ⟨pos u, (mem_faceImage_iff pos hs _).mpr ⟨u, hu, rfl⟩, ?_⟩
      rw [← hplace]
      exact huy
  have hcomp : select ∘ lift = g := by
    funext u
    change select (lift u) = g u
    rcases cases_support _ (hsmall u) with ⟨x, hx⟩ | ⟨e, he⟩
    · rw [hliftPoint u x hx, hgpoint u x hx]
      apply Subtype.ext
      exact Finset.mem_singleton.mp (hselect (retained x)).1
    · obtain ⟨i, hi, hg⟩ := hhalf u e he
      rw [hliftEdge u e he, hg]
      exact IntervalChartRefinement.minimum_selector_eq_half old select hselect (chart e)
        (hindex e) (fine e) (hparent e) (pos u) i (hi.trans (congrArg (· / 2) (hpos u)).symm)
  exact ⟨select, lift, fun v => (hselect v).1, hselectFace, hsimp, hcomp.symm ▸ hc⟩

/-- Every extra component retracts into the subdivision of a single old
edge of the opposite colour. The same edge also works for a one-vertex
component. -/
theorem extra_retraction_in_subdivided_edge {X : Type} {K : PreAbstractSimplicialComplex X}
    (colour : X → Fin 4) (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X)) (c : Color)
    (u : {w : Face (iteratedAmbient K 2).2 | Extra c (RankColouredTetrahedron.row colour w)}) :
    let P := OrdinaryCollarRetraction.colourComplex K (hasColour (opposite c) ∘ colour)
    ∃ e ∈ P, (e : Finset X).card = 2 ∧
      ∀ (v : {w : Face (iteratedAmbient K 2).2 | Extra c (RankColouredTetrahedron.row colour w)}),
        ((subdivisionGraph (iteratedAmbient K 2).2).induce
          {w | Extra c (RankColouredTetrahedron.row colour w)}).Reachable u v →
        ∀ hv : OrdinarySubdivisionMap.inTwoCutCollar (hasColour (opposite c) ∘ colour) v.val,
          {OrdinaryCollarRetraction.retract (hasColour (opposite c) ∘ colour) ⟨v.val, hv⟩} ∈
            iteratedSubcomplex P (simplex e) 3 := by
  intro P
  let p : X → Bool := hasColour (opposite c) ∘ colour
  let E := RankColouredTetrahedron.colourSupport colour (opposite c) u.val
  have hcollar : OrdinarySubdivisionMap.inTwoCutCollar p u.val :=
    (RankColouredTetrahedron.row_inCollar colour (opposite c) u.val).mp
      (pocket_conditions u.property).1
  let start := OrdinaryCollarRetraction.retract p ⟨u.val, hcollar⟩
  have hstart := OrdinaryCollarRetraction.retract_support p ⟨u.val, hcollar⟩
  have hE : E ∈ P := by
    change _ = E at hstart
    rw [← hstart]
    exact originalSupport_mem 3 (vertexOfFace _ start).property
  refine ⟨E, hE, (RankColouredTetrahedron.extra_component_support colour hinj c u u
    SimpleGraph.Reachable.rfl).1, ?_⟩
  intro v huv hv
  let w := OrdinaryCollarRetraction.retract p ⟨v.val, hv⟩
  change {w} ∈ iteratedSubcomplex P (simplex E) 3
  apply (mem_iteratedSubcomplex_iff (B := simplex E) 3 (vertexOfFace _ w).property).mpr
  have he := (RankColouredTetrahedron.extra_component_support colour hinj c u v huv).2
  have hsupport := OrdinaryCollarRetraction.retract_support p ⟨v.val, hv⟩
  change originalSupport P 3 {w} =
    RankColouredTetrahedron.colourSupport colour (opposite c) v.val at hsupport
  change originalSupport P 3 {w} ∈ simplex E
  rw [hsupport, ← he]
  exact ⟨(P.isRelLowerSet_faces hE).1, Finset.Subset.rfl⟩

end

end TetrahedronCollar16
