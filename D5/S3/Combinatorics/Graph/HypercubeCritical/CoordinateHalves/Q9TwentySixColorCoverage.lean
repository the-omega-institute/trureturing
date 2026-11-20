import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColorCoverage
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixCompression
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixColorChecks
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphCoverage

/-! Parity colors of a compressed 26-point coordinate half. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixColorCoverage

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open GirthSliceCounting (degreeThree)
open private paritySide parity_bipartite balanced_subset from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private Graph adjacent labels from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphSearch
open private witnessPerm from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphEncoding
open private decode representatives from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphSearch
open private representative_of_graph from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphCoverage
open private High side from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourExpansion
open private suppress from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCompression
open private count_color_side color_word count_direct_edges cycle_respects_girth from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColorCoverage
open private graphEdgesOfOrder validCycleOfOrder cycleEdges crosses from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColors
open private admissible eligibleGroups mem_eligibleGroups models coloredCases
  checkCase relabelsColor ColorCase.cycles ColorCase.witnesses from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixColors
open private checked from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixColorChecks

attribute [local instance] Classical.propDecidable

private theorem admissible_coloring {V : Type*} [Fintype V] {G : SimpleGraph V}
    {L R : Finset V} (hbip : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hsum : (degreeThree G L).card + (degreeThree G R).card = 14)
    (hsize : let n := min (degreeThree G L).card (degreeThree G R).card
      n = 3 ∨ n = 5 ∨ n = 7)
    (hcount : (∑ v ∈ degreeThree G R, (degreeThree G (G.neighborFinset v)).card) = 9)
    (graph : Graph) (label : Fin 14 ≃ High G L R)
    (hlabel : ∀ i j : Fin 14, adjacent graph i.val j.val = true ↔
      (suppress G L R).Adj (label i) (label j))
    (cycles : List (List Nat)) (hv : cycles.all (validCycleOfOrder 14 graph) = true) :
    ∃ (group : Nat) (reverse : Bool), group < 2 ^ 14 ∧
      (∀ i : Fin 14, group.testBit i.val = (side (label i) ^^ reverse)) ∧
      admissible (graphEdgesOfOrder 14 graph) cycles group = true := by
  let l := (degreeThree G L).card
  let r := (degreeThree G R).card
  let reverse := if l = r then !side (label 0) else decide (l < r)
  obtain ⟨group, hb, hcolor⟩ := color_word label reverse
  refine ⟨group, reverse, hb, hcolor, ?_⟩
  let size := (List.range 14).countP group.testBit
  have hs : size = (if reverse then l else r) := count_color_side label group reverse hcolor
  have hm : size = min l r := by
    rw [hs]
    by_cases he : l = r
    · simp [he]
    · by_cases hlt : l < r
      · simp [reverse, he, hlt, min_eq_left hlt.le]
      · simp [reverse, he, hlt, min_eq_right (Nat.le_of_not_gt hlt)]
  have hsize' : size = 3 ∨ size = 5 ∨ (size = 7 ∧ group.testBit 0 = true) := by
    change min l r = 3 ∨ min l r = 5 ∨ min l r = 7 at hsize
    rcases hsize with h | h | h
    · exact Or.inl (hm.trans h)
    · exact Or.inr (Or.inl (hm.trans h))
    · refine Or.inr (Or.inr ⟨hm.trans h, ?_⟩)
      have hsum' : l + r = 14 := hsum
      have he : l = r := by omega
      have ho := hcolor 0
      change group.testBit 0 = (side (label 0) ^^ reverse) at ho
      rw [ho]
      simp [reverse, he]
  have hdisj : Disjoint L R := by simpa only [Finset.disjoint_coe] using hbip.disjoint
  have he := (count_direct_edges hbip graph label hlabel group reverse hcolor).trans hcount
  unfold admissible
  simp only [Bool.and_eq_true_iff, Bool.or_eq_true_iff, beq_iff_eq]
  exact ⟨⟨or_assoc.symm.mp hsize', he⟩, List.all_eq_true.mpr fun cycle hcycle =>
    decide_eq_true (cycle_respects_girth hdisj hg graph label hlabel group reverse hcolor
      cycle (List.all_eq_true.mp hv cycle hcycle))⟩

private theorem adjacent_decode (code : Nat) (i j : Fin 14) :
    adjacent (decode code) i.val j.val = (code >>> (14 * i.val)).testBit j.val := by
  have hi : i.val < (decode code).size := by simpa [decode] using i.isLt
  rw [adjacent, getElem!_pos (decode code) i.val hi]
  simp only [decode, List.getElem_toArray, List.getElem_map, List.getElem_range,
    Nat.testBit_and, show (0x3fff : Nat) = 2 ^ 14 - 1 by decide, Nat.testBit_two_pow_sub_one,
    j.isLt, decide_true, Bool.and_true]

private theorem coloring_certificate (index : Fin 110) (group : Nat) (hgroup : group < 2 ^ 14)
    (hadm : admissible (graphEdgesOfOrder 14 (decode representatives[index.val]!))
      (ColorCase.cycles coloredCases[index.val]!) group = true) :
    ∃ word, relabelsColor (decode representatives[index.val]!) group word = true := by
  let graph := decode representatives[index.val]!
  let cert := coloredCases[index.val]!
  have h := (Bool.and_eq_true_iff.mp (checked index)).2
  change (eligibleGroups.all fun group =>
    !admissible (graphEdgesOfOrder 14 graph) (ColorCase.cycles cert) group ||
      match List.lookup group (ColorCase.witnesses cert) with
      | none => false
      | some word => relabelsColor graph group word) = true at h
  have hw := List.all_eq_true.mp h group (mem_eligibleGroups hgroup hadm)
  change admissible (graphEdgesOfOrder 14 graph) (ColorCase.cycles cert) group = true at hadm
  simp only [hadm, Bool.not_true, Bool.false_or] at hw
  split at hw
  · cases hw
  · rename_i word _
    exact ⟨word, hw⟩

set_option maxRecDepth 8192 in
private theorem colored_representative (index : Fin 110) (group : Nat) (hgroup : group < 2 ^ 14)
    (hadm : admissible (graphEdgesOfOrder 14 (decode representatives[index.val]!))
      (ColorCase.cycles coloredCases[index.val]!) group = true) :
    ∃ (model : Fin 663) (p : Equiv.Perm (Fin 14)) (reverse : Bool),
      (∀ i j : Fin 14, adjacent (decode representatives[index.val]!) i.val j.val =
        adjacent (decode representatives[models[model.val]!.1]!) (p i).val (p j).val) ∧
      (∀ i : Fin 14, group.testBit i.val =
        (models[model.val]!.2.testBit (p i).val ^^ reverse)) := by
  obtain ⟨word, hw⟩ := coloring_certificate index group hgroup hadm
  let model := word >>> 56
  let color := models[model]!.2
  let reverse := group.testBit 0 != color.testBit (labels word 0)
  unfold relabelsColor at hw
  obtain ⟨⟨⟨⟨hindex, hbound⟩, hn⟩, hmatrix⟩, hcolor⟩ := by
    simpa only [Bool.and_eq_true_iff] using hw
  let p := witnessPerm (order := 14) word
    (fun i hi => of_decide_eq_true (List.all_eq_true.mp hbound _ (List.mem_range.mpr hi)))
    (beq_iff_eq.mp hn)
  have hsize : models.size = 663 := rfl
  refine ⟨⟨model, hsize ▸ of_decide_eq_true hindex⟩, p, reverse, ?_, ?_⟩
  · intro i j
    rw [adjacent_decode _ (p i) (p j)]
    exact beq_iff_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp hmatrix _ (List.mem_range.mpr i.isLt)) _
      (List.mem_range.mpr j.isLt))
  · intro i
    exact beq_iff_eq.mp (List.all_eq_true.mp hcolor _ (List.mem_range.mpr i.isLt))

private theorem colored_model_of_half {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 26) :
    let S := coordinateSlice C b
    let G := (hypercube 9).induce (S : Set (Q 9))
    let L := paritySide S false
    let R := paritySide S true
    ∃ (model : Fin 663) (label : Fin 14 ≃ High G L R) (reverse : Bool),
      (∀ i j : Fin 14, adjacent (decode representatives[models[model.val]!.1]!) i.val j.val =
        true ↔ (suppress G L R).Adj (label i) (label j)) ∧
      (∀ i : Fin 14, models[model.val]!.2.testBit i.val = (side (label i) ^^ reverse)) := by
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := paritySide S false
  let R := paritySide S true
  have hp : G.IsBipartiteWith (L : Set _) (R : Set _) := parity_bipartite S
  have hg : (8 : ℕ∞) ≤ G.egirth :=
    BalancedCubeGirth.eight_le_egirth S (balanced_subset hb (filter_subset _ _))
  obtain ⟨hc, hd, ht, hconn, hcount, hmin⟩ := Q9TwentySixCompression.half_suppression hC hr hb b hs
  have hsum : (degreeThree G L).card + (degreeThree G R).card = 14 := by
    simpa [G, L, R, S, Fintype.card_sum, Fintype.card_coe] using hc
  obtain ⟨index, label, hlabel⟩ := representative_of_graph _ hc hconn hd ht
    (Classical.choice hconn.nonempty)
  let graph := decode representatives[index.val]!
  let cycles := ColorCase.cycles coloredCases[index.val]!
  have hgraph (i j : Fin 14) : adjacent graph i.val j.val = true ↔
      (suppress G L R).Adj (label i) (label j) := by
    rw [show adjacent graph i.val j.val = _ from adjacent_decode _ i j]
    exact hlabel i j
  have hv : cycles.all (validCycleOfOrder 14 graph) = true :=
    (Bool.and_eq_true_iff.mp (checked index)).1
  obtain ⟨group, exchange, hgSize, hcolor, hadm⟩ :=
    admissible_coloring hp hg hsum hmin hcount graph label hgraph cycles hv
  obtain ⟨model, p, reverse, hm, hbit⟩ := colored_representative index group hgSize hadm
  refine ⟨model, p.symm.trans label, exchange ^^ reverse, ?_, ?_⟩
  · intro i j
    have he := hm (p.symm i) (p.symm j)
    rw [p.apply_symm_apply, p.apply_symm_apply] at he
    rw [← he]
    exact hgraph _ _
  · intro i
    have he := hbit (p.symm i)
    rw [p.apply_symm_apply, hcolor] at he
    change models[model.val]!.2.testBit i.val = (side (label (p.symm i)) ^^ (exchange ^^ reverse))
    rw [← Bool.xor_assoc, he, Bool.xor_assoc]
    simp

#print axioms colored_model_of_half

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixColorCoverage
