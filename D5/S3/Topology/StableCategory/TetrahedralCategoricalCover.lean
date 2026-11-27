/- GID: D5/S3/Topology/StableCategory/TetrahedralCategoricalCover
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/TetrahedralCategoricalCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A contractible order complex of dimension at most three has a stable two-piece cover. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.FiniteConeUnionWedge
import D5.S3.Topology.StableCategory.TetrahedralRepeatedRefinement
import D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer
import Mathlib.Order.KrullDimension

/-! The two-colour refinement gives a categorical cover of the iterated
chain poset of a weakly contractible finite poset of height at most four. -/

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

/-- A properly four-coloured finite complex with contractible realization
has, after ordinary subdivision, two induced categorical regions. -/
private theorem two_regions_of_rank {X : Type} [Finite X]
    (K : PreAbstractSimplicialComplex X) (rank : X → Fin 4)
    (proper : ∀ s ∈ K, Set.InjOn rank (s : Set X))
    (b : Vertex K) (point : Space K)
    (contract : (ContinuousMap.id (Space K)).Homotopy (ContinuousMap.const (Space K) point)) :
    ∃ r, let L := (iteratedAmbient K r).2
      ∃ label : (iteratedAmbient K r).1 → Fin 2,
        ∀ j, ∃ c : Vertex L, ReflTransGen Contiguous
          (OrdinaryContiguityLift.includeSubcomplex
            (show colourComplex L (fun v => decide (label v = j)) ≤ L from fun _ hs => hs.1))
          (fun _ => c) := by
  let := Fintype.ofFinite X
  let p (x : X) := decide ((rank x).val < 2)
  let G := paddedColour K p b
  let H := paddedColour K (fun x => !p x) b
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
  have gLe : G ≤ K := paddedColour_le p b
  have hLe : H ≤ K := paddedColour_le _ b
  have gId : ∀ s ∈ G, image s id ∈ K := by
    intro s hs
    rw [image, Finset.image_id]
    exact gLe hs
  have hId : ∀ s ∈ H, image s id ∈ K := by
    intro s hs
    rw [image, Finset.image_id]
    exact hLe hs
  have incId : ∀ s ∈ K, image s id ∈ K := by
    intro s hs
    simpa only [image, Finset.image_id] using hs
  have toG : ∀ s ∈ colourComplex K p, image s id ∈ G := by
    intro s hs
    simpa only [image, Finset.image_id] using (show s ∈ G from Or.inl hs)
  have toH : ∀ s ∈ colourComplex K (fun x => !p x), image s id ∈ H := by
    intro s hs
    simpa only [image, Finset.image_id] using (show s ∈ H from Or.inl hs)
  let gBase : Vertex G := ⟨b.val, Or.inr ⟨Finset.singleton_nonempty _, Finset.Subset.rfl⟩⟩
  let hBase : Vertex H := ⟨b.val, Or.inr ⟨Finset.singleton_nonempty _, Finset.Subset.rfl⟩⟩
  let gReal := realizationInclusion gLe
  let hReal := realizationInclusion hLe
  have realization_support {A : PreAbstractSimplicialComplex X} (hA : A ≤ K)
      (fA : ∀ s ∈ A, image s id ∈ K) (s : Finset X) (hs : s ∈ A) (z : Space A)
      (hz : z.val ∈ faceSimplex s) :
      (realizationInclusion hA z).val ∈ faceSimplex (faceImage (ofTotal id fA) hs) := by
    rwa [ofTotal_faceImage, image, Finset.image_id]
  have inclusion_null {A : PreAbstractSimplicialComplex X} (hA : A ≤ K) :
      (realizationInclusion hA).Homotopy (ContinuousMap.const (Space A) point) := by
    simpa only [ContinuousMap.id_comp, ContinuousMap.const_comp] using
      contract.compContinuousMap (realizationInclusion hA)
  have connected : ∀ x y : Vertex K, (skeleton K).Reachable x y := by
    have : ContractibleSpace (Space K) :=
      (contractible_iff_id_nullhomotopic (Space K)).mpr ⟨point, ⟨contract⟩⟩
    exact TetrahedralGraphIteration.skeleton_reachable_of_preconnected_realization K
  obtain ⟨depth, label, labels⟩ := TetrahedralRepeatedRefinement.eventually_contracts_bicolour
    id incId p id id toG toH rg pg rg ph gBase hBase id gId id hId
    ReflTransGen.refl ReflTransGen.refl connected
    gReal hReal (realization_support gLe gId) (realization_support hLe hId)
    point point (inclusion_null gLe) (inclusion_null hLe)
  refine ⟨depth, label, fun j => ?_⟩
  obtain ⟨c, hc⟩ := labels j
  refine ⟨c, ?_⟩
  have eq : ofTotal (K := colourComplex (iteratedAmbient K depth).2
      (fun x => decide (label x = j))) (iterate id incId depth).val
      (fun s hs => (iterate id incId depth).property s hs.1) =
      OrdinaryContiguityLift.includeSubcomplex
        (show colourComplex (iteratedAmbient K depth).2 (fun x => decide (label x = j))
          ≤ (iteratedAmbient K depth).2 from fun _ hs => hs.1) := by
    funext v
    exact Subtype.ext (congrFun (identity_at_depth K incId depth) v.val)
  exact eq ▸ hc

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
  obtain ⟨r, label, contracts⟩ := two_regions_of_rank K rank proper b point contract
  let := finite_at_depth K r
  exact ⟨r + 2, transfer_lower_cover r 2
    (InducedCategoricalCover.has_categorical_cover_of_partition label contracts)⟩

end

end D5.S3.Topology.StableCategory.TetrahedralCategoricalCover
