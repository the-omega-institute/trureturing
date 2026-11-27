/- GID: D5/S3/Topology/StableCategory/TetrahedralCategoricalCover
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/TetrahedralCategoricalCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A nullhomotopic three-dimensional subcomplex has a relative stable two-piece cover. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.FiniteConeUnionWedge
import D5.S3.Topology.StableCategory.TetrahedralRepeatedRefinement
import D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer
import Mathlib.Order.KrullDimension

/-! The two-colour refinement gives a categorical cover for a nullhomotopic
inclusion of a properly four-coloured complex, and hence for the iterated
chain poset of a contractible finite poset of height at most four. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.TetrahedralCategoricalCover

open BarycentricGraphDistance (Vertex)
open BarycentricBaseRigidity (Contiguous faceImage skeleton)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open OrdinaryCollarRetraction (colourComplex)
open OrdinaryContiguityLift (ofTotal)
open OrdinarySubdivisionTransfer (finiteSpaceSubdivision transfer_lower_cover)
open OrdinarySubdivisionMap (iterate)
open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open D5.S3.Geometry.FiniteConeUnionWedge (realizationInclusion)
open D5.S3.Geometry.FiniteConeCollapse (faceSimplex)
open D5.S3.Geometry.FiniteAlexanderDualCollapse (simplex)
open ConnectedCategoryGraft (HasCategoricalCover)
open private image from D5.S3.Topology.OrdinarySubdivisionMap
open private ofTotal_faceImage from D5.S3.Topology.StableCategory.OrdinaryContiguityLift
open private chainComplex from D5.S3.Topology.SubdivisionCategoricalCover
open private exists_vertex_in_star from D5.S3.Topology.GeometricGraphTermination
open private finite_at_depth from D5.S3.Topology.StableCategory.TetrahedralRepeatedRefinement
open Relation (ReflTransGen)

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

private def paddedColour {X : Type} (K : PreAbstractSimplicialComplex X)
    (p : X → Bool) (b : Vertex K) : PreAbstractSimplicialComplex X :=
  colourComplex K p ⊔ simplex {b.val}

private theorem paddedColour_le {X : Type} {K : PreAbstractSimplicialComplex X}
    (p : X → Bool) (b : Vertex K) : paddedColour K p b ≤ K := by
  apply sup_le (fun _ hs => hs.1)
  intro s hs
  exact (K.isRelLowerSet_faces b.property).2 hs.2 hs.1

private theorem paddedColour_rank {X : Type} {K : PreAbstractSimplicialComplex X}
    (rank : X → Fin 4) (proper : ∀ s ∈ K, Set.InjOn rank (s : Set X))
    (p : X → Bool) (b : Vertex K)
    (hblock : ∀ x y, p x = true → p y = true →
      (rank x).val % 2 = (rank y).val % 2 → rank x = rank y) :
    let q (x : X) : Fin 2 := ⟨(rank x).val % 2, Nat.mod_lt _ Nat.zero_lt_two⟩
    ∀ s ∈ paddedColour K p b, Set.InjOn q (s : Set X) := by
  intro q s hs x hx y hy h
  change s ∈ colourComplex K p ∨ s ∈ simplex {b.val} at hs
  rcases hs with hs | hs
  · exact proper s hs.1 hx hy
      (hblock x y (hs.2 x hx) (hs.2 y hy) (congrArg Fin.val h))
  · exact (Finset.mem_singleton.mp (hs.2 hx)).trans (Finset.mem_singleton.mp (hs.2 hy)).symm

private theorem inclusion_image {X : Type} {A K : PreAbstractSimplicialComplex X}
    (hAK : A ≤ K) : ∀ s ∈ A, image s id ∈ K := by
  intro s hs
  rw [image, Finset.image_id]
  exact hAK hs

private theorem identity_at_depth {X : Type} (K : PreAbstractSimplicialComplex X)
    (mem : ∀ s ∈ K, image s id ∈ K) (r : ℕ) :
    (iterate id mem r).val = id := by
  induction r with
  | zero => rfl
  | succ r ih =>
    funext v
    apply Subtype.ext
    change image v.val (iterate id mem r).val = v.val
    rw [ih, image, Finset.image_id]

/-- A nullhomotopic inclusion of a properly four-coloured finite subcomplex
has, after ordinary subdivision, two induced regions categorical in the
subdivided ambient complex. -/
theorem two_regions_of_rank {X : Type} [Fintype X]
    {A K : PreAbstractSimplicialComplex X} (hAK : A ≤ K) (rank : X → Fin 4)
    (proper : ∀ s ∈ A, Set.InjOn rank (s : Set X))
    (b : Vertex A) (point : Space K)
    (contract : (realizationInclusion hAK).Homotopy (ContinuousMap.const (Space A) point))
    (connected : ∀ x y : Vertex K, (skeleton K).Reachable x y) :
    ∃ r, let D := (iteratedAmbient A r).2
      let L := (iteratedAmbient K r).2
      let inc := iterate (K := A) (L := K) id (inclusion_image hAK) r
      ∃ label : (iteratedAmbient A r).1 → Fin 2,
        ∀ j, ∃ c : Vertex L, ReflTransGen Contiguous
          (ofTotal (K := colourComplex D (fun v => decide (label v = j)))
            inc.val (fun s hs => inc.property s hs.1))
          (fun _ => c) := by
  let p (x : X) := decide ((rank x).val < 2)
  let G := paddedColour A p b
  let H := paddedColour A (fun x => !p x) b
  let rg (x : X) : Fin 2 := ⟨(rank x).val % 2, Nat.mod_lt _ Nat.zero_lt_two⟩
  have pg := paddedColour_rank rank proper p b (by
    intro x y hx hy h
    have hx' : (rank x).val < 2 := of_decide_eq_true hx
    have hy' : (rank y).val < 2 := of_decide_eq_true hy
    apply Fin.ext
    exact (Nat.mod_eq_of_lt hx').symm.trans (h.trans (Nat.mod_eq_of_lt hy')))
  have ph := paddedColour_rank rank proper (fun x => !p x) b (by
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
  have gLe : G ≤ A := paddedColour_le p b
  have hLe : H ≤ A := paddedColour_le _ b
  have toG : ∀ s ∈ colourComplex A p, image s id ∈ G :=
    inclusion_image (fun _ hs => Or.inl hs)
  have toH : ∀ s ∈ colourComplex A (fun x => !p x), image s id ∈ H :=
    inclusion_image (fun _ hs => Or.inl hs)
  let gBase : Vertex G := ⟨b.val, Or.inr ⟨Finset.singleton_nonempty _, Finset.Subset.rfl⟩⟩
  let hBase : Vertex H := ⟨b.val, Or.inr ⟨Finset.singleton_nonempty _, Finset.Subset.rfl⟩⟩
  let gId := inclusion_image (gLe.trans hAK)
  let hId := inclusion_image (hLe.trans hAK)
  let gReal := realizationInclusion (gLe.trans hAK)
  let hReal := realizationInclusion (hLe.trans hAK)
  have realization_support {D : PreAbstractSimplicialComplex X} (hD : D ≤ K)
      (fD : ∀ s ∈ D, image s id ∈ K) (s : Finset X) (hs : s ∈ D) (z : Space D)
      (hz : z.val ∈ faceSimplex s) :
      (realizationInclusion hD z).val ∈ faceSimplex (faceImage (ofTotal id fD) hs) := by
    rwa [ofTotal_faceImage, image, Finset.image_id]
  have inclusion_null {D : PreAbstractSimplicialComplex X} (hD : D ≤ A) :
      (realizationInclusion (hD.trans hAK)).Homotopy (ContinuousMap.const (Space D) point) := by
    have hcomp : (realizationInclusion hAK).comp (realizationInclusion hD) =
        realizationInclusion (hD.trans hAK) := by
      apply ContinuousMap.ext
      intro z
      exact Subtype.ext rfl
    simpa only [hcomp, ContinuousMap.const_comp] using
      contract.compContinuousMap (realizationInclusion hD)
  exact TetrahedralRepeatedRefinement.eventually_contracts_bicolour
    id (inclusion_image hAK) p id id toG toH rg pg rg ph gBase hBase id gId id hId
    ReflTransGen.refl ReflTransGen.refl connected
    gReal hReal (realization_support (gLe.trans hAK) gId)
    (realization_support (hLe.trans hAK) hId)
    point point (inclusion_null gLe) (inclusion_null hLe)

section MeetingFaces

open BarycentricGraphDistance (Face)
open BarycentricBaseRigidity (sd vertexOfFace)
open OrdinarySubdivisionMap (cutFace)
open OrdinaryContiguityLift (Simplicial comp_chains include_subcomplex_simplicial lift_iterates)
open private faceOrderMap from D5.S3.Topology.OrdinarySubdivisionMap
open private first from D5.S3.Topology.OrdinaryCollarRetraction
open private descending_collar_maps mapCollar map_collar_simplicial
  from D5.S3.Topology.StableCategory.OrdinaryCollarContiguity

attribute [local instance] Classical.propDecidable

/-- The subcomplex of flags all of whose faces meet the selected vertices. -/
def meetingFaceComplex {U : Type} (D : PreAbstractSimplicialComplex U) (p : U → Bool) :
    PreAbstractSimplicialComplex (Face D) :=
  colourComplex (sd D) (fun a => decide (cutFace p a).Nonempty)

private theorem meeting_face_chain {U V : Type} [Finite U]
    {D : PreAbstractSimplicialComplex U} {L : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : ∀ s ∈ D, image s f ∈ L) (p : U → Bool) (c : Vertex L)
    (hc : ReflTransGen Contiguous
      (ofTotal (K := colourComplex D p) f (fun s hs => hf s hs.1)) (fun _ => c)) :
    ReflTransGen Contiguous
      (ofTotal (K := meetingFaceComplex D p) (iterate f hf 1).val
        (fun s hs => (iterate f hf 1).property s hs.1))
      (fun _ => vertexOfFace L ⟨{c.val}, c.property⟩) := by
  let q (a : Face D) := decide (cutFace p a).Nonempty
  let cut : {a : Face D // q a = true} →o Face (colourComplex D p) :=
    (first (K := D) p).comp ⟨fun a => ⟨a.val, of_decide_eq_true a.property⟩, fun _ _ h => h⟩
  have old : ∀ s ∈ colourComplex D p, image s f ∈ L := fun s hs => hf s hs.1
  let inc : {a : Face D // q a = true} →o Face L :=
    (faceOrderMap f hf).comp ⟨Subtype.val, fun _ _ h => h⟩
  let reduced := (faceOrderMap f old).comp cut
  have hcut : ReflTransGen Contiguous (mapCollar q inc) (mapCollar q reduced) := by
    apply descending_collar_maps
    intro a
    change image (cutFace p a.val) f ⊆ image a.val.val f
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  let g : U → V := fun _ => c.val
  have hg : ∀ s ∈ colourComplex D p, image s g ∈ L := by
    intro s hs
    change s.image (fun _ => c.val) ∈ L
    simpa only [Finset.image_const ((colourComplex D p).isRelLowerSet_faces hs).1] using c.property
  have hgchain : ReflTransGen Contiguous (ofTotal f old) (ofTotal g hg) := by
    have hmap : ofTotal g hg = (fun _ => c) := by
      funext a
      exact Subtype.ext rfl
    exact hmap.symm ▸ hc
  have hlift := lift_iterates f g old hg hgchain 1
  let pre := mapCollar q cut
  have hp : Simplicial pre := by
    intro s hs
    simpa only [Finset.union_idempotent] using map_collar_simplicial q cut s hs
  let post : Vertex (sd L) → Vertex (sd L) := id
  have hrest := comp_chains pre post hp (include_subcomplex_simplicial (le_refl (sd L))) hlift
  have hjoin : post ∘ ofTotal (iterate f old 1).val (iterate f old 1).property ∘ pre =
      mapCollar q reduced := by
    funext v
    exact Subtype.ext rfl
  have hconst : post ∘ ofTotal (iterate g hg 1).val (iterate g hg 1).property ∘ pre =
      (fun _ => vertexOfFace L ⟨{c.val}, c.property⟩) := by
    funext v
    apply Subtype.ext
    apply Subtype.ext
    change ((pre v).val.val).image (fun _ => c.val) = {c.val}
    exact Finset.image_const ((colourComplex D p).isRelLowerSet_faces (pre v).val.property).1 _
  have hstart : mapCollar q inc =
      ofTotal (K := meetingFaceComplex D p) (iterate f hf 1).val
        (fun s hs => (iterate f hf 1).property s hs.1) := by
    funext v
    exact Subtype.ext rfl
  rw [hjoin, hconst] at hrest
  rw [← hstart]
  exact hcut.trans hrest

/-- One further subdivision turns the two induced regions into a simplicial
cover. Each flag belongs to the piece selected by a vertex of its least face. -/
theorem two_meeting_face_pieces_of_rank {X : Type} [Fintype X]
    {A K : PreAbstractSimplicialComplex X} (hAK : A ≤ K) (rank : X → Fin 4)
    (proper : ∀ s ∈ A, Set.InjOn rank (s : Set X))
    (b : Vertex A) (point : Space K)
    (contract : (realizationInclusion hAK).Homotopy (ContinuousMap.const (Space A) point))
    (connected : ∀ x y : Vertex K, (skeleton K).Reachable x y) :
    ∃ r, let D := (iteratedAmbient A r).2
      let L := (iteratedAmbient K r).2
      let inc := iterate (K := A) (L := K) id (inclusion_image hAK) (r + 1)
      ∃ label : (iteratedAmbient A r).1 → Fin 2,
        (meetingFaceComplex D (fun x => decide (label x = 0)) ⊔
          meetingFaceComplex D (fun x => decide (label x = 1)) = sd D) ∧
        ∀ j : Fin 2, ∃ c : Vertex (sd L), ReflTransGen Contiguous
          (ofTotal (K := meetingFaceComplex D (fun x => decide (label x = j)))
            inc.val (fun s hs => inc.property s hs.1))
          (fun _ => c) := by
  obtain ⟨r, label, contracts⟩ := two_regions_of_rank hAK rank proper b point contract connected
  let D := (iteratedAmbient A r).2
  let := finite_at_depth A r
  refine ⟨r, label, ?_, ?_⟩
  · refine le_antisymm (sup_le (fun _ hs => hs.1) (fun _ hs => hs.1)) ?_
    intro s hs
    obtain ⟨a, ha⟩ := hs.1
    obtain ⟨m, _, hm⟩ := Finite.exists_le_minimal (p := fun f : Face D => f ∈ s) ha
    have hleast (u : Face D) (hu : u ∈ s) : m ≤ u := by
      by_cases h : m = u
      · exact h.le
      rcases hs.2.1 hm.1 hu h with hmu | hum
      · exact hmu.le
      · exact hm.2 hu hum.le
    obtain ⟨x, hx⟩ := (D.isRelLowerSet_faces m.property).1
    have hmem (j : Fin 2) (hj : label x = j) :
        s ∈ meetingFaceComplex D (fun u => decide (label u = j)) := by
      refine ⟨hs, fun u hu => decide_eq_true ?_⟩
      exact ⟨x, Finset.mem_filter.mpr ⟨hleast u hu hx, decide_eq_true hj⟩⟩
    have hlabel : label x = 0 ∨ label x = 1 :=
      (Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp (label x).isLt)).imp Fin.ext Fin.ext
    exact hlabel.elim (fun h => Or.inl (hmem 0 h)) (fun h => Or.inr (hmem 1 h))
  · intro j
    obtain ⟨c, hc⟩ := contracts j
    let inc := iterate (K := A) (L := K) id (inclusion_image hAK) r
    exact ⟨vertexOfFace _ ⟨{c.val}, c.property⟩,
      meeting_face_chain inc.val inc.property (fun x => decide (label x = j)) c hc⟩

end MeetingFaces

/-- For a nonempty finite poset of dimension at most three, a contraction
of its order-complex realization yields a categorical lower cover of size
two after finitely many ordinary subdivisions. -/
theorem two_lower_sets_of_contractible_order_complex
    (P : Type) [Finite P] [PartialOrder P]
    (dimension : Order.krullDim P ≤ (3 : ℕ∞))
    (point : Space (chainComplex P))
    (contract : (ContinuousMap.id (Space (chainComplex P))).Homotopy
      (ContinuousMap.const (Space (chainComplex P)) point)) :
    ∃ r, @HasCategoricalCover (finiteSpaceSubdivision P r).1
      (finiteSpaceSubdivision P r).2 2 := by
  let K := chainComplex P
  have hle (x : P) : Order.height x ≤ (3 : ℕ∞) :=
    WithBot.coe_le_coe.mp ((Order.height_le_krullDim x).trans dimension)
  have finiteHeight (x : P) : Order.height x < ⊤ :=
    (hle x).trans_lt (ENat.natCast_lt_top 3)
  let rank (x : P) : Fin 4 := ⟨(Order.height x).toNat, Nat.lt_succ_of_le
    (ENat.toNat_le_of_le_natCast (hle x))⟩
  have strict : StrictMono rank := by
    intro x y hxy
    have h := Order.height_strictMono hxy (finiteHeight x)
    rw [← ENat.natCast_toNat (finiteHeight x).ne, ← ENat.natCast_toNat (finiteHeight y).ne] at h
    exact_mod_cast h
  have proper (s : Finset P) (hs : s ∈ K) : Set.InjOn rank (s : Set P) := by
    intro x hx y hy eq
    by_contra hn
    rcases hs.2 hx hy hn with h | h
    · exact (strict (lt_of_le_of_ne h hn)).ne eq
    · exact (strict (lt_of_le_of_ne h (Ne.symm hn))).ne eq.symm
  let := Fintype.ofFinite P
  obtain ⟨b, _⟩ := exists_vertex_in_star point
  have self : realizationInclusion (le_refl K) = ContinuousMap.id (Space K) := by
    apply ContinuousMap.ext
    intro z
    exact Subtype.ext rfl
  have null : (realizationInclusion (le_refl K)).Homotopy (ContinuousMap.const (Space K) point) := by
    rw [self]
    exact contract
  have connected : ∀ x y : Vertex K, (skeleton K).Reachable x y := by
    have : ContractibleSpace (Space K) :=
      (contractible_iff_id_nullhomotopic (Space K)).mpr ⟨point, ⟨contract⟩⟩
    exact TetrahedralGraphIteration.skeleton_reachable_of_preconnected_realization K
  obtain ⟨r, label, contracts⟩ :=
    two_regions_of_rank (le_refl K) rank proper b point null connected
  let := finite_at_depth K r
  refine ⟨r + 2, transfer_lower_cover r 2
    (InducedCategoricalCover.has_categorical_cover_of_partition
      (K := (iteratedAmbient K r).2) label ?_)⟩
  intro j
  obtain ⟨c, hc⟩ := contracts j
  refine ⟨c, ?_⟩
  have eq : ofTotal (K := colourComplex (iteratedAmbient K r).2
      (fun x => decide (label x = j))) (iterate id (inclusion_image (le_refl K)) r).val
      (fun s hs => (iterate id (inclusion_image (le_refl K)) r).property s hs.1) =
      OrdinaryContiguityLift.includeSubcomplex
        (show colourComplex (iteratedAmbient K r).2 (fun x => decide (label x = j))
          ≤ (iteratedAmbient K r).2 from fun _ hs => hs.1) := by
    funext v
    exact Subtype.ext (congrFun (identity_at_depth K (inclusion_image (le_refl K)) r) v.val)
  exact eq ▸ hc

end

end D5.S3.Topology.StableCategory.TetrahedralCategoricalCover
