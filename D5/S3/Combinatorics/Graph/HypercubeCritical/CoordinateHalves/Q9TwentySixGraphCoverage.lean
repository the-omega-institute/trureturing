import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphCertificates1
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphCertificates2
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphCertificates3
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphCertificates4

/-! The order-fourteen cubic graphs used to classify 26-point cube halves. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphCoverage

open private Graph candidatesOfOrder frontier search search_frontier from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphSearch
open private classify_graph from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphEncoding
open private decode relabels relabelingCheck relabels_sound representatives witness_of_branch from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphSearch
open private branches1 checkedPart1 from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphCertificates1
open private branches2 checkedPart2 from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphCertificates2
open private branches3 checkedPart3 from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphCertificates3
open private branches4 checkedPart4 from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphCertificates4

private def branches : List (Nat × Nat × List Nat) :=
  branches1 ++ branches2 ++ branches3 ++ branches4

set_option maxRecDepth 8192 in
set_option maxHeartbeats 120000000 in
private theorem frontier_checked :
    frontier 14 6 0 (Array.replicate 14 0) 1 =
      branches.map (fun (code, discovered, _) => (decode code, discovered)) := by
  decide +kernel

private theorem candidate_has_witness {graph : Graph} (hg : graph ∈ candidatesOfOrder 14) :
    ∃ witness, relabels graph witness = true := by
  change graph ∈ search 14 (6 + 8) 0 1 (Array.replicate 14 0) at hg
  rw [search_frontier, frontier_checked] at hg
  obtain ⟨state, hstate, hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨branch, hb, he⟩ := List.mem_map.mp hstate
  have hchecked : branches.all relabelingCheck = true := by
    simp only [branches, List.all_append, checkedPart1, checkedPart2, checkedPart3, checkedPart4, Bool.and_true]
  rw [← he] at hg
  exact witness_of_branch branch (List.all_eq_true.mp hchecked branch hb) hg

private theorem representative_of_graph {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcard : Fintype.card V = 14) (hconn : G.Connected)
    (hregular : G.IsRegularOfDegree 3)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False) (start : V) :
    ∃ (index : Fin 110) (label : Fin 14 ≃ V), ∀ i j : Fin 14,
      (representatives[index.val]! >>> (14 * i.val)).testBit j.val = true ↔
        G.Adj (label i) (label j) := by
  obtain ⟨number, hn⟩ := classify_graph G hcard hconn hregular htriangle start
  obtain ⟨word, hw⟩ := candidate_has_witness hn
  exact relabels_sound G number word hw

#print axioms representative_of_graph

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixGraphCoverage
