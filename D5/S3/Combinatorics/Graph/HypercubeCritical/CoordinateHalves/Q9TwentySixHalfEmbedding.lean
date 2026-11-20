import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourHalfEmbedding
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixColorCoverage
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixDistanceChecks
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixPlacementChecks
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixReconstruction

/-! A 26-point half of a balanced cubic support of order 72 forces a 20-point half. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixHalfEmbedding

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open Q9GrayPlacementNormalForm (normalize)
open private parity_bipartite coordinate_slice_card_sum coordinate_slice_low_independent from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private expanded_graph from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourModelCoverage
open private distance from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourModelDistances
open private normalized_embedding_of_model from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourHalfEmbedding
open private decode representatives from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphSearch
open private models from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixColors
open private colored_model_of_half from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixColorCoverage
open private modelAt reorder from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixModelDistances
open private valid_model from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixDistanceChecks
open private possiblePlacement placements_checked from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixPlacementChecks
open private listedHalves twenty_cut_of_listed_half from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixReconstruction
open private oppositeSize from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourEmbeddingCheck
open private liftPoint oppositeSize_lift from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCubeMetric
open private cube_action_regular_balanced from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixNormalizeProbe

attribute [local instance] Classical.propDecidable

set_option maxRecDepth 8192 in
private theorem model_of_half {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 26) :
    ∃ (index : Fin 663) (point : Fin 26 ≃ (coordinateSlice C b : Set (Q 9))),
      ∀ i j : Fin 26, distance (modelAt index) i.val j.val = 1 ↔
        (hypercube 9).Adj (point i).val (point j).val := by
  obtain ⟨index, label, reverse, he, hc⟩ := colored_model_of_half hC hr hb b hs
  obtain ⟨_, hlen, hbound, hinj, hmatrix, _, _⟩ := valid_model index
  obtain ⟨point, hp⟩ := expanded_graph (order := 14) (lowCount := 12)
    (parity_bipartite (coordinateSlice C b)) ((Fintype.card_coe _).trans hs)
    (fun _ _ hAdj hx hy => coordinate_slice_low_independent hr hb hAdj hx hy)
    (decode representatives[models[index.val]!.1]!) models[index.val]!.2 label reverse he hc hlen
  let perm (i : Fin 26) : Fin 26 := ⟨reorder index i, hbound i⟩
  have hperm : Function.Injective perm := fun i j h => hinj i j (congrArg Fin.val h)
  let e := Equiv.ofBijective perm ⟨hperm, Finite.surjective_of_injective hperm⟩
  exact ⟨index, e.trans point, fun i j => (hmatrix i j).trans (hp (perm i) (perm j))⟩

private theorem listed_halves_nodup :
    listedHalves.all (fun half => decide half.Nodup) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- A 26/46 coordinate cut forces a 20/52 cut of the same support. -/
theorem exists_twenty_cut_of_twenty_six {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 26) :
    ∃ (j : Fin 9) (c : Bool), (C.filter (fun x => x j = c)).card = 20 := by
  classical
  obtain ⟨index, point, hpoint⟩ := model_of_half hC hr hb b hs
  obtain ⟨hlen, _, _, _, _, hparent, hpath⟩ := valid_model index
  obtain ⟨g, σ, placed, ⟨center, hcenter⟩, hflip, hcut, hplaced, hbound, hn, hm⟩ :=
    normalized_embedding_of_model b _ hlen point hpoint hparent hpath
  have hT := cube_action_regular_balanced g σ hflip hr hb
  have hfalse : coordinateSlice (C.image g) false = (coordinateSlice C b).image g := by
    ext y
    constructor
    · intro hy
      obtain ⟨hmem, hy⟩ := mem_filter.mp hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hmem
      exact mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, (hcut x).mp hy⟩, rfl⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      obtain ⟨hx, he⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨mem_image.mpr ⟨x, hx, rfl⟩, (hcut x).mpr he⟩
  have hparts := coordinate_slice_card_sum (C.image g)
  rw [hfalse, card_image_of_injective _ g.injective, hs,
    card_image_of_injective _ g.injective, hC] at hparts
  have hop : oppositeSize placed = 46 := by
    rw [oppositeSize_lift placed hbound,
      Q9TwentyTwoReconstruction.reconstruction_size hT.1 hT.2 _ hn hm]
    omega
  have hcheck := List.all_eq_true.mp (placements_checked index) placed hplaced
  rw [possiblePlacement, hop] at hcheck
  simp only [bne_self_eq_false, Bool.false_or] at hcheck
  obtain ⟨half, hlisted, hset⟩ := List.any_eq_true.mp hcheck
  have he := beq_iff_eq.mp hset
  have hhalf (x : BitVec 9) : x ∈ half ↔ cubeBitVec 9 x ∈ coordinateSlice (C.image g) false := by
    rw [← List.mem_toFinset, ← he, List.mem_toFinset]
    exact hm x
  have h20 := twenty_cut_of_listed_half hT.1 hT.2
    (of_decide_eq_true (List.all_eq_true.mp listed_halves_nodup half hlisted)) hhalf hlisted
  let j := σ.symm 1
  have hcoord (x : Q 9) : g x 1 = true ↔ x j = !center j := by
    rw [hcenter]
    change (x j != center j) = true ↔ x j = !center j
    cases x j <;> cases center j <;> decide
  refine ⟨j, !center j, ?_⟩
  rw [Finset.filter_image, show C.filter (fun x => g x 1 = true) =
    C.filter (fun x => x j = !center j) by ext x; simp only [mem_filter, hcoord],
    card_image_of_injective _ g.injective] at h20
  exact h20

#print axioms exists_twenty_cut_of_twenty_six

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixHalfEmbedding
