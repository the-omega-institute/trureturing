/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SmallComponentBoundary142
   generality: I
   mirror-B: none(waiver:isolated-verification)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Bounds the actual exterior vertex boundary of small balanced cubic nine-cube supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8OrientedFiberNeighborhood
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityFoldedBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourHalfEmbedding

/-! Folding each parity class gives a closed neighborhood in `Q 8`. The
opposite parity class of the support lies in the corresponding open
neighborhood, and removing it leaves at least 71 exterior vertices. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SmallComponentBoundary142

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open CoordinateHalves.BalancedHalfCardinality (half_cardinality)
open CubeClosedNeighborhoodRecurrence (closedNeighborhood)
open Q8OrientedFiberNeighborhood (closedNeighborhood_lower_bounds sideCount)
open Q9ParityFoldedBoundary (parity parityPart dropCoordinate cubic_parityPart_card
  coordinate_half_parity_bounds card_image_dropCoordinate card_projected_parity_half
  card_neighbor_eq_card_closed_neighbor_image)
open private parity_eq_not_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityFoldedBoundary
open private reindex reindex_regular reindex_balanced reindex_slice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

attribute [local instance] Classical.propDecidable

private def openNeighborhood (S : Finset (Q 9)) : Finset (Q 9) :=
  univ.filter fun y => ∃ x ∈ S, (hypercube 9).Adj x y

/-- The vertices outside `C` adjacent in the ambient nine-cube to a vertex of `C`. -/
def exteriorBoundary (C : Finset (Q 9)) : Finset (Q 9) :=
  openNeighborhood C \ C

private theorem mem_openNeighborhood {S : Finset (Q 9)} {y : Q 9} :
    y ∈ openNeighborhood S ↔ ∃ x ∈ S, (hypercube 9).Adj x y := by
  simp [openNeighborhood]

private theorem parity_of_mem_neighborhood {C : Finset (Q 9)} {p : Bool} {y : Q 9}
    (hy : y ∈ openNeighborhood (parityPart C p)) : parity y = !p := by
  obtain ⟨x, hx, hxy⟩ := mem_openNeighborhood.mp hy
  rw [parity_eq_not_of_adj hxy, (mem_filter.mp hx).2]

private theorem opposite_part_subset_neighborhood {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (p : Bool) :
    parityPart C (!p) ⊆ openNeighborhood (parityPart C p) := by
  intro y hy
  obtain ⟨hyC, hyparity⟩ := mem_filter.mp hy
  let G := (hypercube 9).induce (C : Set (Q 9))
  let v : (C : Set (Q 9)) := ⟨y, hyC⟩
  have hcard : (G.neighborFinset v).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hr.degree_eq v]
  obtain ⟨u, hu⟩ := card_pos.mp (by rw [hcard]; decide : 0 < (G.neighborFinset v).card)
  have hyu : (hypercube 9).Adj y u.val := (G.mem_neighborFinset v u).mp hu
  have huparity : parity u.val = p := by
    rw [parity_eq_not_of_adj hyu, hyparity, Bool.not_not]
  exact mem_openNeighborhood.mpr ⟨u.val, mem_filter.mpr ⟨u.property, huparity⟩, hyu.symm⟩

private theorem card_openNeighborhood_parity {C : Finset (Q 9)} (p : Bool) :
    (openNeighborhood (parityPart C p)).card =
      (closedNeighborhood ((parityPart C p).image (dropCoordinate (Fin.last 8)))).card := by
  have hfold := card_neighbor_eq_card_closed_neighbor_image (Fin.last 8) p (parityPart C p)
    (fun _ hx => (mem_filter.mp hx).2)
  rw [openNeighborhood, hfold]
  congr 1
  ext y
  simp only [closedNeighborhood, mem_filter, mem_univ, true_and]
  apply exists_congr
  intro x
  change (_ ∧ (x = y ∨ hammingDist x y = 1)) ↔ (_ ∧ hammingDist y x ≤ 1)
  rw [hammingDist_comm y x, ← hammingDist_eq_zero]
  exact and_congr_right fun _ => by omega

private abbrev foldedPart (C : Finset (Q 9)) (p : Bool) : Finset (Q 8) :=
  (parityPart C p).image (dropCoordinate (Fin.last 8))

private theorem foldedPart_card {C : Finset (Q 9)} {m : ℕ} (hC : C.card = 6 * m)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (p : Bool) :
    (foldedPart C p).card = 3 * m :=
  (card_image_dropCoordinate (Fin.last 8) p _ (fun _ hx => (mem_filter.mp hx).2)).trans
    (cubic_parityPart_card hC hr p)

private theorem foldedPart_sideCount {C : Finset (Q 9)} (p : Bool) (k : Fin 8) (b : Bool) :
    sideCount (foldedPart C p) k b =
      (parityPart (C.filter fun x => x ((Fin.last 8).succAbove k) = b) p).card :=
  card_projected_parity_half (Fin.last 8) k C b p

private theorem exterior_parity_lower_bound {C : Finset (Q 9)} {m k : ℕ}
    (hC : C.card = 6 * m)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (p : Bool)
    (hfold : 3 * m + k ≤ (closedNeighborhood (foldedPart C p)).card) :
    k ≤ (openNeighborhood (parityPart C p) \ C).card := by
  have hneighbors : 3 * m + k ≤ (openNeighborhood (parityPart C p)).card := by
    rw [card_openNeighborhood_parity]
    exact hfold
  have hdiff : openNeighborhood (parityPart C p) \ C =
      openNeighborhood (parityPart C p) \ parityPart C (!p) := by
    ext y
    simp only [mem_sdiff, parityPart, mem_filter]
    exact and_congr_right fun hy => by simp [parity_of_mem_neighborhood hy]
  rw [hdiff, card_sdiff_of_subset (opposite_part_subset_neighborhood hr p),
    cubic_parityPart_card hC hr (!p)]
  omega

private theorem exteriorBoundary_card_ge_of_folds {C : Finset (Q 9)} {m k : ℕ}
    (hC : C.card = 6 * m)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hfold : ∀ p, 3 * m + k ≤ (closedNeighborhood (foldedPart C p)).card) :
    2 * k ≤ (exteriorBoundary C).card := by
  let L := openNeighborhood (parityPart C false) \ C
  let R := openNeighborhood (parityPart C true) \ C
  have hsplit : exteriorBoundary C = L ∪ R := by
    ext y
    simp only [L, R, exteriorBoundary, mem_union, mem_sdiff, mem_openNeighborhood]
    constructor
    · rintro ⟨⟨x, hx, hxy⟩, hy⟩
      cases hp : parity x with
      | false => exact Or.inl ⟨⟨x, mem_filter.mpr ⟨hx, hp⟩, hxy⟩, hy⟩
      | true => exact Or.inr ⟨⟨x, mem_filter.mpr ⟨hx, hp⟩, hxy⟩, hy⟩
    · rintro (⟨⟨x, hx, hxy⟩, hy⟩ | ⟨⟨x, hx, hxy⟩, hy⟩) <;>
        exact ⟨⟨x, (mem_filter.mp hx).1, hxy⟩, hy⟩
  have hdisjoint : Disjoint L R := by
    apply disjoint_left.mpr
    intro y hyL hyR
    have hL := parity_of_mem_neighborhood (mem_sdiff.mp hyL).1
    have hR := parity_of_mem_neighborhood (mem_sdiff.mp hyR).1
    exact Bool.noConfusion (hL.symm.trans hR)
  have hL : k ≤ L.card := exterior_parity_lower_bound hC hr false (hfold false)
  have hR : k ≤ R.card := exterior_parity_lower_bound hC hr true (hfold true)
  rw [hsplit, card_union_of_disjoint hdisjoint]
  omega

private theorem exteriorBoundary_card_ge {C : Finset (Q 9)} {m : ℕ}
    (hm : m = 12 ∨ m = 13) (hC : C.card = 6 * m)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hmargins : ∀ (j : Fin 9) (b p : Bool),
      11 ≤ (parityPart (C.filter fun x => x j = b) p).card) :
    142 ≤ (exteriorBoundary C).card := by
  apply exteriorBoundary_card_ge_of_folds (k := 71) hC hr
  intro p
  have hS := foldedPart_card hC hr p
  have hmargins' (i : Fin 4) (b : Bool) :
      11 ≤ sideCount (foldedPart C p) (Fin.castAddEmb 4 i) b := by
    rw [foldedPart_sideCount]
    exact hmargins _ b p
  rcases hm with rfl | rfl
  · exact (closedNeighborhood_lower_bounds _ hmargins').1 hS
  · exact (closedNeighborhood_lower_bounds _ hmargins').2 hS

/-- An order-72 balanced induced cubic support with at least 26 vertices in
every coordinate half has at least 142 distinct exterior neighbors. -/
theorem exteriorBoundary_card_ge_142_of_card_eq_72 {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ (j : Fin 9) (b : Bool), 26 ≤ (C.filter fun x => x j = b).card) :
    142 ≤ (exteriorBoundary C).card := by
  have h72 : C.card = 6 * 12 := hC
  apply exteriorBoundary_card_ge (Or.inl rfl) h72 hr
  intro j b p
  have ⟨_, hbalance, _⟩ := coordinate_half_parity_bounds h72 hr hb j b p
  have hsize := hhalf j b
  omega

private theorem half_card_ge_26_of_no_twenty_half {C : Finset (Q 9)}
    (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (h20 : ∀ (j : Fin 9) (b : Bool), (C.filter fun x => x j = b).card ≠ 20) :
    ∀ (j : Fin 9) (b : Bool), 26 ≤ (C.filter fun x => x j = b).card := by
  intro j b
  let e := Equiv.swap j (0 : Fin 9)
  let T := C.image (reindex e)
  have hT : T.card = 72 := by
    rw [show T = C.image (reindex e) from rfl, card_image_of_injective _ (reindex e).injective, hC]
  have hslice : (coordinateSlice T b).card = (C.filter fun x => x j = b).card := by
    rw [show coordinateSlice T b = (C.filter fun x => x j = b).image (reindex e) from
      reindex_slice C j b, card_image_of_injective _ (reindex e).injective]
  have h22 := CoordinateHalves.Q9TwentyTwoPairedExclusion.no_twenty_two_half
    hT (reindex_regular hr e) (reindex_balanced hb e) b
  have h24 := CoordinateHalves.Q9TwentyFourHalfEmbedding.no_twenty_four_half
    hT (reindex_regular hr e) (reindex_balanced hb e) b
  rw [hslice] at h22 h24
  have h72 : C.card = 6 * 12 := hC
  obtain ⟨hmin, hmod⟩ := half_cardinality h72 hr hb j b
  have size_bound (n : ℕ) (hmin : 60 ≤ 3 * n) (heven : n % 2 = 0)
      (h20 : n ≠ 20) (h22 : n ≠ 22) (h24 : n ≠ 24) : 26 ≤ n := by omega
  exact size_bound _ hmin hmod (h20 j b) h22 h24

/-- For order 72, excluding 20-vertex halves suffices because the 22- and
24-vertex halves are already ruled out. -/
theorem exteriorBoundary_card_ge_142_of_card_eq_72_of_no_twenty_half {C : Finset (Q 9)}
    (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (h20 : ∀ (j : Fin 9) (b : Bool), (C.filter fun x => x j = b).card ≠ 20) :
    142 ≤ (exteriorBoundary C).card :=
  exteriorBoundary_card_ge_142_of_card_eq_72 hC hr hb
    (half_card_ge_26_of_no_twenty_half hC hr hb h20)

/-- Excluding 20-vertex halves in an order-72 balanced induced cubic support
forces at least 144 distinct exterior neighbors. -/
theorem exteriorBoundary_card_ge_144_of_card_eq_72_of_no_twenty_half {C : Finset (Q 9)}
    (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (h20 : ∀ (j : Fin 9) (b : Bool), (C.filter fun x => x j = b).card ≠ 20) :
    144 ≤ (exteriorBoundary C).card := by
  have h72 : C.card = 6 * 12 := hC
  have hmargins (j : Fin 9) (b p : Bool) :
      11 ≤ (parityPart (C.filter fun x => x j = b) p).card := by
    have ⟨_, hbalance, _⟩ := coordinate_half_parity_bounds h72 hr hb j b p
    have hsize := half_card_ge_26_of_no_twenty_half hC hr hb h20 j b
    omega
  apply exteriorBoundary_card_ge_of_folds (k := 72) h72 hr
  intro p
  apply Q8OrientedFiberNeighborhood.closedNeighborhood_card_ge_108 _ (foldedPart_card h72 hr p)
  intro i b
  rw [foldedPart_sideCount]
  exact hmargins _ b p

#print axioms exteriorBoundary_card_ge_144_of_card_eq_72_of_no_twenty_half

/-- Every order-78 balanced induced cubic support has at least 142 distinct
exterior neighbors. -/
theorem exteriorBoundary_card_ge_142_of_card_eq_78 {C : Finset (Q 9)} (hC : C.card = 78)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    142 ≤ (exteriorBoundary C).card := by
  have h78 : C.card = 6 * 13 := hC
  exact exteriorBoundary_card_ge (Or.inr rfl) h78 hr fun j b p =>
    (coordinate_half_parity_bounds h78 hr hb j b p).2.2 rfl

#print axioms exteriorBoundary
#print axioms exteriorBoundary_card_ge_142_of_card_eq_72
#print axioms exteriorBoundary_card_ge_142_of_card_eq_72_of_no_twenty_half
#print axioms exteriorBoundary_card_ge_142_of_card_eq_78

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SmallComponentBoundary142
