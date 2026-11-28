/- GID: D5/S3/Topology/StableCategory/ThreePieceCategoricalCover
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/ThreePieceCategoricalCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A three-piece categorical cover of contractible complexes through dimension five. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.FourPieceCategoricalCover
import D5.S3.Topology.StableCategory.LebesgueStarAssignment
import D5.S3.Topology.StableCategory.TetrahedralAsymmetricIteration

/-! The terminal step of the asymmetric three-piece construction. All maps
advance by the same ordinary subdivision depth. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.ThreePieceCategoricalCover

open BarycentricGraphDistance (Face Vertex)
open BarycentricBaseRigidity (Contiguous faceImage sd skeleton vertexOfFace)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open OrdinaryCollarRetraction (colourComplex)
open OrdinarySubdivisionMap (iterate)
open OrdinaryContiguityLift (Simplicial ofTotal of_total_simplicial includeSubcomplex
  include_subcomplex_simplicial comp_chains subdivide subdivide_of_total lift_chain
  iterated_ambient_add)
open FourPieceCategoricalCover (CategoricalMapCover)
open TetrahedralCategoricalCover (meetingFaceComplex)
open LebesgueStarAssignment (iteratedRealization)
open TetrahedralAsymmetricIteration (eventually_contracts_graph_against_complex)
open D5.S3.Geometry.FiniteConeCollapse (faceSimplex)
open D5.S3.Geometry.FiniteAlexanderDualCollapse (simplex)
open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open D5.S3.Geometry.FiniteConeUnionWedge (realizationInclusion)
open GeometricGraphTermination (realizedVertexMap)
open Relation (ReflTransGen)
open scoped ContinuousMap
open private subdivide_simplicial from
  D5.S3.Topology.StableCategory.TerminalCarrierIteration
open private selectedColour region region_le include_image regionMap collarAt collarAt_le
  collars_cover collar_factor finite_at_depth id_simplicial
  subdivision_comp face_image_include cover_subdivide cover_pullback cover_of_chain from
  D5.S3.Topology.StableCategory.FourPieceCategoricalCover
open private paddedColour paddedColour_le paddedColour_rank inclusion_image
  meeting_face_chain from D5.S3.Topology.StableCategory.TetrahedralCategoricalCover
open private ofTotal_faceImage from D5.S3.Topology.StableCategory.OrdinaryContiguityLift
open private depthFintype depthDecEq from
  D5.S3.Topology.StableCategory.LebesgueStarAssignment
open private image from D5.S3.Topology.OrdinarySubdivisionMap
open private mem_faceImage_iff from D5.S3.Topology.GraphSubdivisionIntervals
open private extendVertexMap linearMap_mem_faceImage exists_vertex_in_star
  from D5.S3.Topology.GeometricGraphTermination
open private singleton_mem_of_mem from D5.S3.Topology.BarycentricBaseRigidity

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X
attribute [local instance] Classical.propDecidable

variable {X U Y : Type}
variable {D : PreAbstractSimplicialComplex X} {B : PreAbstractSimplicialComplex U}
variable {L : PreAbstractSimplicialComplex Y}

/-- Ordinary subdivision of a simplicial map defined on the actual vertices. -/
def mapAt (f : Vertex D → Vertex L) (hf : Simplicial f) :
    (n : ℕ) → {g : Vertex (iteratedAmbient D n).2 → Vertex (iteratedAmbient L n).2 //
      Simplicial g}
  | 0 => ⟨f, hf⟩
  | n + 1 =>
    let g := mapAt f hf n
    ⟨subdivide g.val g.property, subdivide_simplicial g.val g.property⟩

private theorem subdivide_congr {f g : Vertex D → Vertex L}
    (e : f = g) (hf : Simplicial f) (hg : Simplicial g) :
    subdivide f hf = subdivide g hg := by
  cases e
  rfl

private theorem map_at_congr {f g : Vertex D → Vertex L}
    (e : f = g) (hf : Simplicial f) (hg : Simplicial g) (n : ℕ) :
    (mapAt f hf n).val = (mapAt g hg n).val := by
  cases e
  rfl

private theorem map_at_comp (f : Vertex D → Vertex B) (g : Vertex B → Vertex L)
    (hf : Simplicial f) (hg : Simplicial g) (n : ℕ) :
    (mapAt (g ∘ f) (hg.comp hf) n).val = (mapAt g hg n).val ∘ (mapAt f hf n).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let a := mapAt f hf n
    let b := mapAt g hg n
    let c := mapAt (g ∘ f) (hg.comp hf) n
    exact (subdivide_congr ih c.property (b.property.comp a.property)).trans
      (subdivision_comp a.val b.val a.property b.property)

private theorem map_at_of_total (f : X → Y) (hf : ∀ s ∈ D, image s f ∈ L) (n : ℕ) :
    (mapAt (ofTotal f hf) (of_total_simplicial f hf) n).val =
      ofTotal (iterate f hf n).val (iterate f hf n).property := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let a := mapAt (ofTotal f hf) (of_total_simplicial f hf) n
    let b := iterate f hf n
    exact (subdivide_congr ih a.property (of_total_simplicial b.val b.property)).trans
      (subdivide_of_total b.val b.property)

private theorem chain_at [Finite X] {f g : Vertex D → Vertex L}
    (hf : Simplicial f) (hg : Simplicial g) (chain : ReflTransGen Contiguous f g) (n : ℕ) :
    ReflTransGen Contiguous (mapAt f hf n).val (mapAt g hg n).val := by
  induction n with
  | zero => exact chain
  | succ n ih =>
    let := finite_at_depth D n
    exact lift_chain (mapAt f hf n).property (mapAt g hg n).property ih

private theorem cover_at {I : Type} [Finite X] (f : Vertex D → Vertex L)
    (hf : Simplicial f) (cover : CategoricalMapCover I f) (n : ℕ) :
    CategoricalMapCover I (mapAt f hf n).val := by
  induction n with
  | zero => exact cover
  | succ n ih =>
    let := finite_at_depth D n
    exact cover_subdivide _ (mapAt f hf n).property ih

private theorem region_map_at [Fintype X] (label : X → Fin 2) (i : Fin 2) (n : ℕ) :
    (mapAt (includeSubcomplex (region_le D label i))
      (include_subcomplex_simplicial (region_le D label i)) n).val =
      regionMap D label i n := by
  have eq : includeSubcomplex (region_le D label i) =
      ofTotal id (include_image D label i) := by
    funext v
    exact Subtype.ext rfl
  exact (map_at_congr eq _ _ n).trans (map_at_of_total id (include_image D label i) n)

private theorem cover_on_collar {I : Type} [Fintype X]
    (f : Vertex D → Vertex L) (hf : Simplicial f) (label : X → Fin 2)
    (i : Fin 2) (n : ℕ)
    (h : CategoricalMapCover I
      (mapAt (f ∘ includeSubcomplex (region_le D label i))
        (hf.comp (include_subcomplex_simplicial (region_le D label i))) (n + 1)).val) :
    CategoricalMapCover I
      ((mapAt f hf (n + 1)).val ∘ includeSubcomplex (collarAt_le D label i n)) := by
  obtain ⟨cut, hcut, chain⟩ := collar_factor D label i n
  let F := mapAt f hf (n + 1)
  have eq := map_at_comp (includeSubcomplex (region_le D label i)) f
    (include_subcomplex_simplicial (region_le D label i)) hf (n + 1)
  rw [region_map_at (D := D) label i (n + 1)] at eq
  rw [eq] at h
  refine cover_of_chain ?_ (cover_pullback cut hcut _ h)
  have hc := comp_chains (id : Vertex (collarAt D label i n) → _) F.val id_simplicial
    F.property chain
  simpa only [Function.comp_id, Function.comp_assoc] using hc

/-- The colour-1 collar remains a single categorical piece. A two-piece
cover of the parameter map pulls back through the colour-0 collar. -/
theorem three_pieces_of_factor_cover [Fintype X]
    (f : Vertex D → Vertex L) (hf : Simplicial f) (label : X → Fin 2)
    (c : Vertex L)
    (left : ReflTransGen Contiguous
      (f ∘ includeSubcomplex (region_le D label 1)) (fun _ => c))
    (pre : Vertex (region D label 0) → Vertex B) (hpre : Simplicial pre)
    (post : Vertex B → Vertex L) (hpost : Simplicial post)
    (right : ReflTransGen Contiguous
      (f ∘ includeSubcomplex (region_le D label 0)) (post ∘ pre))
    (parameterCover : ∃ n, CategoricalMapCover (Fin 2) (mapAt post hpost (n + 1)).val) :
    ∃ n, CategoricalMapCover (Fin 3) (mapAt f hf n).val := by
  obtain ⟨n, hparam⟩ := parameterCover
  let leftMap := f ∘ includeSubcomplex (region_le D label 1)
  let hleftMap : Simplicial leftMap := hf.comp (include_subcomplex_simplicial _)
  have hleft : CategoricalMapCover Unit leftMap := by
    refine ⟨fun _ => region D label 1, fun _ => le_refl _, fun _ hs => ⟨(), hs⟩, ?_⟩
    intro _
    exact ⟨c, left⟩
  have hc₁ := cover_on_collar f hf label 1 n (cover_at leftMap hleftMap hleft (n + 1))

  let rightMap := f ∘ includeSubcomplex (region_le D label 0)
  let hrightMap : Simplicial rightMap := hf.comp (include_subcomplex_simplicial _)
  have hchain := chain_at hrightMap (hpost.comp hpre) right (n + 1)
  rw [map_at_comp pre post hpre hpost (n + 1)] at hchain
  have hpull := cover_pullback (mapAt pre hpre (n + 1)).val
    (mapAt pre hpre (n + 1)).property (mapAt post hpost (n + 1)).val hparam
  have hc₀ := cover_on_collar f hf label 0 n (cover_of_chain hchain hpull)

  obtain ⟨P, hP, coverP, catP⟩ := hc₁
  obtain ⟨Q, hQ, coverQ, catQ⟩ := hc₀
  let R : Fin 3 → PreAbstractSimplicialComplex (iteratedAmbient D (n + 1)).1 :=
    Fin.cases (P ()) Q
  have hR (j : Fin 3) : R j ≤ (iteratedAmbient D (n + 1)).2 := by
    refine Fin.cases (motive := fun j => R j ≤ (iteratedAmbient D (n + 1)).2) ?_ ?_ j
    · exact (hP ()).trans (collarAt_le D label 1 n)
    · intro k
      exact (hQ k).trans (collarAt_le D label 0 n)
  refine ⟨n + 1, R, hR, ?_, ?_⟩
  · intro s hs
    obtain ⟨i, hi⟩ := collars_cover D label n s hs
    have hi' : i = 0 ∨ i = 1 :=
      (Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp i.isLt)).imp Fin.ext Fin.ext
    rcases hi' with rfl | rfl
    · obtain ⟨k, hk⟩ := coverQ s hi
      exact ⟨k.succ, hk⟩
    · obtain ⟨u, hu⟩ := coverP s hi
      cases u
      exact ⟨0, hu⟩
  · intro j
    refine Fin.cases (motive := fun j => ∃ z : Vertex (iteratedAmbient L (n + 1)).2,
      ReflTransGen Contiguous
        ((mapAt f hf (n + 1)).val ∘ includeSubcomplex (hR j)) (fun _ => z)) ?_ ?_ j
    · exact catP ()
    · exact catQ

/-- The identity remains the identity through ordinary subdivision. -/
private theorem map_at_id (D : PreAbstractSimplicialComplex X)
    (hf : Simplicial (id : Vertex D → Vertex D)) (n : ℕ) :
    (mapAt id hf n).val = id := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let A := (iteratedAmbient D n).2
    have step : subdivide (id : Vertex A → Vertex A) id_simplicial = id := by
      funext v
      apply Subtype.ext
      apply Subtype.ext
      exact face_image_include (le_refl A) v.val.val v.val.property
    exact (subdivide_congr ih (mapAt id hf n).property id_simplicial).trans step

private theorem extend_vertex_image (fallback : Vertex L) (f : Vertex B → Vertex L)
    (s : Finset U) (hs : s ∈ B) :
    image s (extendVertexMap fallback f) = faceImage f hs := by
  ext y
  rw [Finset.mem_image, mem_faceImage_iff]
  constructor
  · rintro ⟨x, hx, he⟩
    let v : Vertex B := ⟨x, singleton_mem_of_mem hs hx⟩
    exact ⟨v, hx, (dite_eq_left v.property).symm.trans he⟩
  · rintro ⟨v, hv, he⟩
    exact ⟨v.val, hv, (dite_eq_left v.property).trans he⟩

private theorem two_pieces_of_supported_rank_nonempty [Fintype U] [Fintype Y]
    (fallback : Vertex L) (f : Vertex B → Vertex L) (hf : Simplicial f)
    (rank : U → Fin 4) (proper : ∀ s ∈ B, Set.InjOn rank (s : Set U)) (b : Vertex B)
    (real : C(Space B, Space L))
    (supported : ∀ s (hs : s ∈ B) (z : Space B), z.val ∈ faceSimplex s →
      (real z).val ∈ faceSimplex (faceImage f hs))
    (point : Space L) (contract : real.Homotopy (ContinuousMap.const (Space B) point))
    (connected : ∀ x y : Vertex L, (skeleton L).Reachable x y) :
    ∃ n, CategoricalMapCover (Fin 2) (mapAt f hf (n + 1)).val := by
  let total := extendVertexMap fallback f
  have htotal : ∀ s ∈ B, image s total ∈ L := by
    intro s hs
    change image s (extendVertexMap fallback f) ∈ L
    rw [extend_vertex_image fallback f s hs]
    exact hf s hs
  have total_eq : ofTotal total htotal = f := by
    funext v
    apply Subtype.ext
    exact dite_eq_left v.property

  let p (x : U) : Bool := decide ((rank x).val < 2)
  let G := paddedColour B p b
  let H := paddedColour B (fun x => !p x) b
  let parity (x : U) : Fin 2 := ⟨(rank x).val % 2, Nat.mod_lt _ Nat.zero_lt_two⟩
  have rankG := paddedColour_rank rank proper p b (by
    intro x y hx hy h
    have hx' : (rank x).val < 2 := of_decide_eq_true hx
    have hy' : (rank y).val < 2 := of_decide_eq_true hy
    apply Fin.ext
    exact (Nat.mod_eq_of_lt hx').symm.trans (h.trans (Nat.mod_eq_of_lt hy')))
  have rankH := paddedColour_rank rank proper (fun x => !p x) b (by
    intro x y hx hy h
    have hx' : ¬ (rank x).val < 2 := by simpa [p] using hx
    have hy' : ¬ (rank y).val < 2 := by simpa [p] using hy
    have hxmax := (rank x).isLt
    have hymax := (rank y).isLt
    apply Fin.ext
    have hxle : 2 ≤ (rank x).val := Nat.le_of_not_gt hx'
    have hyle : 2 ≤ (rank y).val := Nat.le_of_not_gt hy'
    have hdivx : (rank x).val / 2 = 1 := Nat.div_eq_of_lt_le hxle hxmax
    have hdivy : (rank y).val / 2 = 1 := Nat.div_eq_of_lt_le hyle hymax
    have ex := Nat.mod_add_div (rank x).val 2
    have ey := Nat.mod_add_div (rank y).val 2
    rw [hdivx] at ex
    rw [hdivy] at ey
    exact ex.symm.trans ((congrArg (fun z : ℕ => z + 2 * 1) h).trans ey))
  have gLe : G ≤ B := paddedColour_le p b
  have hLe : H ≤ B := paddedColour_le _ b
  have toG : ∀ s ∈ colourComplex B p, image s id ∈ G :=
    inclusion_image (fun _ hs => Or.inl hs)
  have toH : ∀ s ∈ colourComplex B (fun x => !p x), image s id ∈ H :=
    inclusion_image (fun _ hs => Or.inl hs)
  let gBase : Vertex G := ⟨b.val, Or.inr ⟨Finset.singleton_nonempty _, Finset.Subset.rfl⟩⟩
  let hBase : Vertex H := ⟨b.val, Or.inr ⟨Finset.singleton_nonempty _, Finset.Subset.rfl⟩⟩

  let restricted {A : PreAbstractSimplicialComplex U} (hA : A ≤ B) :=
    real.comp (realizationInclusion hA)
  have carried {A : PreAbstractSimplicialComplex U} (hA : A ≤ B)
      (s : Finset U) (hs : s ∈ A) (z : Space A) (hz : z.val ∈ faceSimplex s) :
      (restricted hA z).val ∈
        faceSimplex (faceImage (ofTotal total (fun t ht => htotal t (hA ht))) hs) := by
    rw [ofTotal_faceImage]
    change (restricted hA z).val ∈ faceSimplex (image s (extendVertexMap fallback f))
    rw [extend_vertex_image fallback f s (hA hs)]
    exact supported s (hA hs) (realizationInclusion hA z) hz
  have null {A : PreAbstractSimplicialComplex U} (hA : A ≤ B) :
      (restricted hA).Homotopy (ContinuousMap.const (Space A) point) := by
    simpa only [restricted, ContinuousMap.const_comp] using
      contract.compContinuousMap (realizationInclusion hA)

  obtain ⟨n, label, cats⟩ :=
    TetrahedralRepeatedRefinement.eventually_contracts_bicolour
      total htotal p id id toG toH parity rankG parity rankH gBase hBase
      total (fun s hs => htotal s (gLe hs)) total (fun s hs => htotal s (hLe hs))
      ReflTransGen.refl ReflTransGen.refl connected
      (restricted gLe) (restricted hLe) (carried gLe) (carried hLe)
      point point (null gLe) (null hLe)

  let A := (iteratedAmbient B n).2
  let : Finite (iteratedAmbient B n).1 := finite_at_depth B n
  let := Fintype.ofFinite (iteratedAmbient B n).1
  let a := iterate total htotal n
  let e := iterate total htotal (n + 1)
  have eq : (mapAt f hf (n + 1)).val = ofTotal e.val e.property :=
    (map_at_congr total_eq.symm hf _ (n + 1)).trans (map_at_of_total total htotal (n + 1))
  refine ⟨n, ?_⟩
  rw [eq]
  let P (j : Fin 2) := meetingFaceComplex A (fun x => decide (label x = j))
  have hP (j : Fin 2) : P j ≤ sd A := fun _ hs => hs.1
  refine ⟨P, hP, ?_, ?_⟩
  · intro s hs
    obtain ⟨a, ha⟩ := hs.1
    obtain ⟨m, _, hm⟩ := Finite.exists_le_minimal (p := fun f : Face A => f ∈ s) ha
    have least (u : Face A) (hu : u ∈ s) : m ≤ u := by
      by_cases h : m = u
      · exact h.le
      rcases hs.2.1 hm.1 hu h with hmu | hum
      · exact hmu.le
      · exact hm.2 hu hum.le
    obtain ⟨x, hx⟩ := (A.isRelLowerSet_faces m.property).1
    refine ⟨label x, hs, fun u hu => decide_eq_true ?_⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨least u hu hx, decide_eq_true rfl⟩⟩
  · intro j
    obtain ⟨c, hc⟩ := cats j
    exact ⟨vertexOfFace _ ⟨{c.val}, c.property⟩,
      meeting_face_chain a.val a.property (fun x => decide (label x = j)) c hc⟩

/-- A supported nullhomotopic map from a properly four-ranked complex has
two categorical restrictions after a common ordinary subdivision. -/
theorem two_pieces_of_supported_rank [Fintype U] [Fintype Y]
    (fallback : Vertex L) (f : Vertex B → Vertex L) (hf : Simplicial f)
    (rank : U → Fin 4) (proper : ∀ s ∈ B, Set.InjOn rank (s : Set U))
    (real : C(Space B, Space L))
    (supported : ∀ s (hs : s ∈ B) (z : Space B), z.val ∈ faceSimplex s →
      (real z).val ∈ faceSimplex (faceImage f hs))
    (point : Space L) (contract : real.Homotopy (ContinuousMap.const (Space B) point))
    (connected : ∀ x y : Vertex L, (skeleton L).Reachable x y) :
    ∃ n, CategoricalMapCover (Fin 2) (mapAt f hf (n + 1)).val := by
  by_cases h : Nonempty (Vertex B)
  · obtain ⟨b⟩ := h
    exact two_pieces_of_supported_rank_nonempty fallback f hf rank proper b
      real supported point contract connected
  · refine ⟨0, fun _ => sd B, fun _ => le_refl _, fun _ hs => ⟨0, hs⟩, ?_⟩
    intro _
    let c := vertexOfFace L ⟨{fallback.val}, fallback.property⟩
    refine ⟨c, ?_⟩
    have eq : (mapAt f hf 1).val ∘ includeSubcomplex (le_refl (sd B)) = (fun _ => c) := by
      funext v
      obtain ⟨x, hx⟩ := (B.isRelLowerSet_faces v.val.property).1
      exact (h ⟨⟨x, singleton_mem_of_mem v.val.property hx⟩⟩).elim
    rw [eq]

/-- Terminal supplier for the asymmetric iteration. Colour 1 is already
categorical and colour 0 factors through a properly four-ranked parameter
whose affine realization is nullhomotopic. -/
theorem three_pieces_of_rank_factor [Fintype X] [Fintype U] [Fintype Y]
    (f : Vertex D → Vertex L) (hf : Simplicial f) (label : X → Fin 2)
    (c : Vertex L)
    (left : ReflTransGen Contiguous
      (f ∘ includeSubcomplex (region_le D label 1)) (fun _ => c))
    (pre : Vertex (region D label 0) → Vertex B) (hpre : Simplicial pre)
    (post : Vertex B → Vertex L) (hpost : Simplicial post)
    (right : ReflTransGen Contiguous
      (f ∘ includeSubcomplex (region_le D label 0)) (post ∘ pre))
    (rank : U → Fin 4) (proper : ∀ s ∈ B, Set.InjOn rank (s : Set U))
    (point : Space L)
    (contract : (realizedVertexMap c post hpost).Homotopy (ContinuousMap.const (Space B) point))
    (connected : ∀ x y : Vertex L, (skeleton L).Reachable x y) :
    ∃ n, CategoricalMapCover (Fin 3) (mapAt f hf n).val := by
  apply three_pieces_of_factor_cover f hf label c left pre hpre post hpost right
  exact two_pieces_of_supported_rank c post hpost rank proper (realizedVertexMap c post hpost)
    (fun _ hs _ hz => linearMap_mem_faceImage c post hs hz) point contract connected

private theorem padded_rank {q : X → Bool} {b : Vertex D}
    {rank : X → Fin 6} {k : ℕ} {r : X → Fin k}
    (proper : ∀ s ∈ D, Set.InjOn rank (s : Set X))
    (recover : ∀ x y, q x = true → q y = true → r x = r y → rank x = rank y) :
    ∀ s ∈ paddedColour D q b, Set.InjOn r (s : Set X) := by
  intro s hs x hx y hy he
  change s ∈ colourComplex D q ∨ s ∈ simplex {b.val} at hs
  rcases hs with hs | hs
  · exact proper s hs.1 hx hy (recover x y (hs.2 x hx) (hs.2 y hy) he)
  · exact (Finset.mem_singleton.mp (hs.2 hx)).trans (Finset.mem_singleton.mp (hs.2 hy)).symm

private theorem contractible_at_depth [Fintype X] (K : PreAbstractSimplicialComplex X)
    [ContractibleSpace (Space K)] (n : ℕ) [Fintype (iteratedAmbient K n).1] :
    ContractibleSpace (Space (iteratedAmbient K n).2) := by
  let U := (iteratedAmbient K n).1
  let C (instances : Fintype U × DecidableEq U) : Prop :=
    letI := instances.1
    letI := instances.2
    ContractibleSpace (Space (iteratedAmbient K n).2)
  have h : C (depthFintype K n, depthDecEq K n) :=
    (iteratedRealization K n).contractibleSpace
  have e : C (depthFintype K n, depthDecEq K n) =
      C ((inferInstance : Fintype U), Classical.decEq U) :=
    congrArg C (Subsingleton.elim _ _)
  exact e.mp h

private theorem cover_of_contractible_rank [Fintype X]
    (K : PreAbstractSimplicialComplex X) [ContractibleSpace (Space K)]
    (rank : X → Fin 6) (proper : ∀ s ∈ K, Set.InjOn rank (s : Set X)) :
    ∃ n, CategoricalMapCover (Fin 3) (K := (iteratedAmbient K n).2)
      (L := (iteratedAmbient K n).2) id := by
  obtain ⟨point, ⟨contract⟩⟩ := id_nullhomotopic (Space K)
  obtain ⟨b, _⟩ := exists_vertex_in_star point
  let p (x : X) : Bool := decide ((rank x).val < 2)
  let G := paddedColour K p b
  let H := paddedColour K (fun x => !p x) b
  let rankG (x : X) : Fin 2 := ⟨(rank x).val % 2, Nat.mod_lt _ Nat.zero_lt_two⟩
  let rankH (x : X) : Fin 4 := ⟨(rank x).val - 2, by
    by_cases h : 2 ≤ (rank x).val
    · exact Nat.sub_lt_left_of_lt_add h (rank x).isLt
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge h))]
      decide⟩
  have properG : ∀ s ∈ G, Set.InjOn rankG (s : Set X) := by
    apply padded_rank proper
    intro x y hx hy he
    have hx' : (rank x).val < 2 := of_decide_eq_true hx
    have hy' : (rank y).val < 2 := of_decide_eq_true hy
    apply Fin.ext
    exact (Nat.mod_eq_of_lt hx').symm.trans ((congrArg Fin.val he).trans (Nat.mod_eq_of_lt hy'))
  have properH : ∀ s ∈ H, Set.InjOn rankH (s : Set X) := by
    apply padded_rank proper
    intro x y hx hy he
    have hx' : 2 ≤ (rank x).val := Nat.le_of_not_gt (by simpa [p] using hx)
    have hy' : 2 ≤ (rank y).val := Nat.le_of_not_gt (by simpa [p] using hy)
    apply Fin.ext
    exact (Nat.sub_add_cancel hx').symm.trans
      ((congrArg (fun r : Fin 4 => r.val + 2) he).trans (Nat.sub_add_cancel hy'))
  have gLe : G ≤ K := paddedColour_le p b
  have hLe : H ≤ K := paddedColour_le _ b
  have gSrc : ∀ s ∈ colourComplex K p, image s id ∈ G :=
    inclusion_image (fun _ hs => Or.inl hs)
  have hSrc : ∀ s ∈ colourComplex K (fun x => !p x), image s id ∈ H :=
    inclusion_image (fun _ hs => Or.inl hs)
  let gBase : Vertex G := ⟨b.val, Or.inr ⟨Finset.singleton_nonempty _, Finset.Subset.rfl⟩⟩
  let hBase : Vertex H := ⟨b.val, Or.inr ⟨Finset.singleton_nonempty _, Finset.Subset.rfl⟩⟩
  let inc := inclusion_image (le_refl K)
  let real := realizationInclusion gLe
  have carried (s : Finset X) (hs : s ∈ G) (z : Space G) (hz : z.val ∈ faceSimplex s) :
      (real z).val ∈ faceSimplex (faceImage (ofTotal id (inclusion_image gLe)) hs) := by
    rw [ofTotal_faceImage, image, Finset.image_id]
    exact hz
  have gNull : real.Homotopy (ContinuousMap.const (Space G) point) := by
    simpa only [ContinuousMap.id_comp, ContinuousMap.const_comp] using
      contract.compContinuousMap real
  obtain ⟨m, colour, ⟨c, hc⟩, W, B, fW, _, ⟨rB, prB⟩, pre, post, hpre, hpost, hright⟩ :=
    eventually_contracts_graph_against_complex id inc p id id gSrc hSrc
      rankG properG gBase hBase rankH properH id (inclusion_image gLe) id (inclusion_image hLe)
      ReflTransGen.refl ReflTransGen.refl real carried point gNull
  let T := (iteratedAmbient K (3 * m)).2
  let : Finite (iteratedAmbient K (3 * m)).1 := finite_at_depth K (3 * m)
  let : Fintype (iteratedAmbient K (3 * m)).1 := Fintype.ofFinite _
  let : Finite W := fW
  let : Fintype W := Fintype.ofFinite _
  let f := ofTotal (iterate id inc (3 * m)).val (iterate id inc (3 * m)).property
  have hf : Simplicial f := of_total_simplicial _ _
  have fid : f = id :=
    (map_at_of_total id inc (3 * m)).symm.trans (map_at_id K id_simplicial (3 * m))
  let label (x : (iteratedAmbient K (3 * m)).1) : Fin 2 := if colour x then 1 else 0
  have leftColour : selectedColour label 1 = colour := by
    funext x
    cases e : colour x <;> simp [selectedColour, label, e]
  have rightColour : selectedColour label 0 = fun x => !colour x := by
    funext x
    cases e : colour x <;> simp [selectedColour, label, e]
  have leftTransfer (q : (iteratedAmbient K (3 * m)).1 → Bool) (eq : q = colour) :
      ReflTransGen Contiguous
        (f ∘ includeSubcomplex (show colourComplex T q ≤ T from fun _ hs => hs.1))
        (fun _ => c) := by
    subst q
    exact hc
  have left := leftTransfer _ leftColour
  have : ContractibleSpace (Space T) := contractible_at_depth K (3 * m)
  have connected : ∀ x y : Vertex T, (skeleton T).Reachable x y :=
    TetrahedralGraphIteration.skeleton_reachable_of_preconnected_realization T
  have rightTransfer (q : (iteratedAmbient K (3 * m)).1 → Bool)
      (eq : q = fun x => !colour x) :
      ∃ a : Vertex (colourComplex T q) → Vertex B, Simplicial a ∧
        ReflTransGen Contiguous
          (f ∘ includeSubcomplex (show colourComplex T q ≤ T from fun _ hs => hs.1))
          (post ∘ a) := by
    subst q
    exact ⟨pre, hpre, hright⟩
  obtain ⟨pre', hpre', right⟩ := rightTransfer _ rightColour
  let postReal := realizedVertexMap c post hpost
  obtain ⟨q, ⟨null⟩⟩ := (id_nullhomotopic (Space T)).comp_left postReal
  have null' : postReal.Homotopy (ContinuousMap.const (Space B) q) := by
    simpa only [ContinuousMap.id_comp] using null
  obtain ⟨d, cover⟩ := three_pieces_of_rank_factor f hf label c left pre' hpre' post hpost
    right rB prB q null' connected
  have eq : (mapAt f hf d).val = id :=
    (map_at_congr fid hf id_simplicial d).trans (map_at_id T id_simplicial d)
  rw [eq] at cover
  refine ⟨3 * m + d, ?_⟩
  have pack := iterated_ambient_add K (3 * m) d
  let Covered (A : Σ U : Type, PreAbstractSimplicialComplex U) :=
    CategoricalMapCover (Fin 3) (K := A.2) (L := A.2) id
  exact pack ▸ (show Covered (iteratedAmbient T d) from cover)

/-- Every finite complex of dimension at most five with contractible realization
admits three categorical subcomplexes at a common ordinary subdivision depth. -/
theorem three_pieces_of_contractible [Fintype X]
    (K : PreAbstractSimplicialComplex X) [ContractibleSpace (Space K)]
    (dimension : ∀ s ∈ K, s.card ≤ 6) :
    ∃ n, CategoricalMapCover (Fin 3) (K := (iteratedAmbient K n).2)
      (L := (iteratedAmbient K n).2) id := by
  let : Fintype (Face K) := Fintype.ofFinite _
  let : Fintype (iteratedAmbient K 1).1 := by
    change Fintype (Face K)
    infer_instance
  have : ContractibleSpace (Space (sd K)) := contractible_at_depth K 1
  obtain ⟨rank, proper⟩ := (ColourGraphJoin.subdivision_rank_colouring K dimension).2
  obtain ⟨d, cover⟩ := cover_of_contractible_rank (sd K) rank proper
  refine ⟨1 + d, ?_⟩
  let Covered (A : Σ U : Type, PreAbstractSimplicialComplex U) :=
    CategoricalMapCover (Fin 3) (K := A.2) (L := A.2) id
  exact iterated_ambient_add K 1 d ▸ (show Covered (iteratedAmbient (sd K) d) from cover)

end
end D5.S3.Topology.StableCategory.ThreePieceCategoricalCover
