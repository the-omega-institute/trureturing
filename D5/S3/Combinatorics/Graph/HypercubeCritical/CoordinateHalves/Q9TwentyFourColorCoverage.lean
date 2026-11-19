import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColors
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCompression
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphEncoding

/-! Transport the finite coloring certificates to graphs labeled by the
twelve high vertices of a coordinate half. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColorCoverage

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open Q9TwentyFourCompression (half_suppression)
open private paritySide from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private suppress from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCompression
open private adjacent decode labels representatives from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphSearch
open private representative_of_graph witnessPerm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphEncoding
open private models coloredCases graphEdges admissible validCycle relabelsColor checkCase checked
  ColorCase.cycles ColorCase.witnesses from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColors

attribute [local instance] Classical.propDecidable

private theorem representative_of_half {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 24) :
    let S := coordinateSlice C b
    let G := (hypercube 9).induce (S : Set (Q 9))
    let J := suppress G (paritySide S false) (paritySide S true)
    ∃ (index : Fin 22) (label : Fin 12 ≃ _), ∀ i j,
      adjacent (decode representatives[index.val]!) i.val j.val = true ↔
        J.Adj (label i) (label j) := by
  obtain ⟨hc, hd, ht, hconn⟩ := half_suppression hC hr hb b hs
  exact representative_of_graph _ hc hconn hd ht (Classical.choice hconn.nonempty)

set_option maxRecDepth 4096 in
private theorem coloring_certificate (index : Fin 22) (group : Nat) (hgroup : group < 4096)
    (hvalid : admissible (graphEdges (decode representatives[index.val]!))
      (ColorCase.cycles coloredCases[index.val]!) group = true) :
    ∃ word, relabelsColor (decode representatives[index.val]!) group word = true := by
  let graph := decode representatives[index.val]!
  let cert := coloredCases[index.val]!
  have hc := checked index
  unfold checkCase at hc
  change ((ColorCase.cycles cert).all (validCycle graph) &&
    (List.range 4096).all fun group =>
      !admissible (graphEdges graph) (ColorCase.cycles cert) group ||
        match List.lookup group (ColorCase.witnesses cert) with
        | none => false
        | some witness => relabelsColor graph group witness) = true at hc
  have hw := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 group
    (List.mem_range.mpr hgroup)
  change admissible (graphEdges graph) (ColorCase.cycles cert) group = true at hvalid
  simp only [hvalid, Bool.not_true, Bool.false_or] at hw
  split at hw
  · cases hw
  · rename_i word _
    exact ⟨word, hw⟩

/-- A certified coloring yields both an adjacency-preserving permutation and
agreement of the parity classes up to a global exchange. -/
private theorem colored_representative (index : Fin 22) (group : Nat) (hgroup : group < 4096)
    (hvalid : admissible (graphEdges (decode representatives[index.val]!))
      (ColorCase.cycles coloredCases[index.val]!) group = true) :
    ∃ (model : Fin 53) (p : Equiv.Perm (Fin 12)) (reverse : Bool),
      (∀ i j : Fin 12, adjacent (decode representatives[index.val]!) i.val j.val =
        adjacent (decode models[model.val]!.1) (p i).val (p j).val) ∧
      (∀ i : Fin 12, group.testBit i.val = (models[model.val]!.2.testBit (p i).val ^^ reverse)) := by
  obtain ⟨word, hw⟩ := coloring_certificate index group hgroup hvalid
  let modelIndex := word >>> 48
  let model := models[modelIndex]!
  let reverse := group.testBit 0 != model.2.testBit (labels word 0)
  change (decide (modelIndex < models.size) &&
    (List.range 12).all (fun i => decide (labels word i < 12)) &&
    (((List.range 12).map (labels word)).eraseDups.length == 12) &&
    (List.range 12).all (fun i => (List.range 12).all fun j =>
      adjacent (decode representatives[index.val]!) i j ==
        adjacent (decode model.1) (labels word i) (labels word j)) &&
    (List.range 12).all (fun i => group.testBit i == (model.2.testBit (labels word i) ^^ reverse)))
      = true at hw
  obtain ⟨⟨⟨⟨hindex, hbound⟩, hnodup⟩, hgraph⟩, hcolor⟩ := by
    simpa only [Bool.and_eq_true_iff] using hw
  let p := witnessPerm word (fun i hi =>
    of_decide_eq_true (List.all_eq_true.mp hbound _ (List.mem_range.mpr hi)))
    (beq_iff_eq.mp hnodup)
  have hsize : models.size = 53 := rfl
  refine ⟨⟨modelIndex, hsize ▸ of_decide_eq_true hindex⟩, p, reverse, ?_, ?_⟩
  · intro i j
    exact beq_iff_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp hgraph _ (List.mem_range.mpr i.isLt)) _
      (List.mem_range.mpr j.isLt))
  · intro i
    exact beq_iff_eq.mp (List.all_eq_true.mp hcolor _ (List.mem_range.mpr i.isLt))

#print axioms representative_of_half
#print axioms colored_representative

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColorCoverage
