/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodMultiport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.claim; result=D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.result; claim=D5/S3/Combinatorics/Graph/StarForming/HeawoodMultiport.claim
   digest: Actual second-cut module and its dissociation twenty-set. -/

import D5.S3.Combinatorics.Graph.StarForming.DissociationCover
import D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity
import D5.S3.Combinatorics.Graph.StarForming.FiniteMasks

/-! Original rows, selection, cut edges and finite certificate proofs from
formal/StarForming/HeawoodMultiport.lean at subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0. The displayed
34-vertex module refutes its proposed local cap nineteen. It does not
refute global cubic compensation and makes no exact beta claim. -/


namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodMultiport

open DissociationCover
open StarFormingDissociationRefutation

def rows : List (List Nat) := [
  [1, 5, 6],
  [0, 2, 7],
  [1, 3, 8],
  [2, 4, 9],
  [3, 5, 10],
  [0, 4, 11],
  [0, 12, 18],
  [1, 13, 19],
  [2, 14, 18],
  [3, 15, 19],
  [4, 16, 18],
  [5, 17, 19],
  [6, 17, 28],
  [7, 14, 20],
  [8, 13],
  [9, 16],
  [10, 15],
  [11, 12],
  [6, 8, 10],
  [7, 9, 11],
  [13, 27, 30],
  [28, 29, 31],
  [29, 30, 32],
  [30, 31, 33],
  [27, 31],
  [28, 32, 33],
  [27, 29, 33],
  [20, 24, 26],
  [12, 21, 25],
  [21, 22, 26],
  [20, 22, 23],
  [21, 23, 24],
  [22, 25],
  [23, 25, 26]]

def adjacency (first second : Fin 34) : Prop :=
  ((rows.getD first.val []).contains second.val) = true

instance : DecidableRel adjacency :=
  fun first second => inferInstanceAs (Decidable
    (((rows.getD first.val []).contains second.val) = true))

def chosen : List Nat := [0, 1, 3, 4, 8, 11, 12, 13, 15, 16, 18, 19, 20, 22, 24, 26, 28, 31, 32, 33]

def selected (vertex : Fin 34) : Prop := chosen.contains vertex.val = true

instance : DecidablePred selected :=
  fun vertex => inferInstanceAs (Decidable (chosen.contains vertex.val = true))

def selectedDegree (vertex : Fin 34) : Nat :=
  ((List.finRange 34).filter (fun neighbor =>
    decide (adjacency vertex neighbor ∧ selected neighbor))).length

def unjoined (first second : Fin 34) : Prop :=
  adjacency first second ∧
    ¬ (first.val = 12 ∧ second.val = 28 ∨ first.val = 28 ∧ second.val = 12 ∨
       first.val = 13 ∧ second.val = 20 ∨ first.val = 20 ∧ second.val = 13)

instance : DecidableRel unjoined :=
  fun first second => inferInstanceAs (Decidable
    (adjacency first second ∧
      ¬ (first.val = 12 ∧ second.val = 28 ∨ first.val = 28 ∧ second.val = 12 ∨
         first.val = 13 ∧ second.val = 20 ∨ first.val = 20 ∧ second.val = 13)))

def color (vertex : Fin 34) : Nat :=
  if vertex.val < 20 then
    if 6 ≤ vertex.val ∧ vertex.val < 12 then (vertex.val + 1) % 2
    else vertex.val % 2
  else if vertex.val < 27 then 0 else 1

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem witness_dissociates : Dissociates adjacency selected := by
  unfold Dissociates
  decide

theorem witness_cardinality :
    ((List.finRange 34).filter (fun vertex => decide (selected vertex))).length = 20 := by
  decide

theorem simple_subcubic :
    (∀ vertex, ¬ adjacency vertex vertex) ∧
    (∀ first second, adjacency first second ↔ adjacency second first) ∧
    (∀ vertex, ((List.finRange 34).filter (fun neighbor =>
      decide (adjacency vertex neighbor))).length ≤ 3) := by
  decide

theorem bipartite : ∀ first second, adjacency first second → color first ≠ color second := by
  decide

theorem attachment_isolates :
    ∀ vertex : Fin 34, [12, 13, 20, 28].contains vertex.val = true →
      selected vertex ∧ ∀ neighbor, unjoined vertex neighbor → ¬ selected neighbor := by
  decide

theorem external_port_profile :
    (∀ vertex : Fin 34, [15, 16, 24, 32].contains vertex.val = true →
      selected vertex ∧ selectedDegree vertex = 1) ∧
    (∀ vertex : Fin 34, [14, 17].contains vertex.val = true → ¬ selected vertex) ∧
    (∀ vertex : Fin 34, ((List.finRange 34).filter (fun neighbor =>
      decide (adjacency vertex neighbor))).length = 2 ↔
        [14, 15, 16, 17, 24, 32].contains vertex.val = true) := by
  decide


def graph : SimpleGraph (Fin 34) where
  Adj := adjacency
  symm := ⟨fun a b h => (simple_subcubic.2.1 a b).mp h⟩
  loopless := ⟨simple_subcubic.1⟩

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel adjacency)

def selectedSet : Finset (Fin 34) := Finset.univ.filter selected

/-- The actual module is bipartite and subcubic, with the original six
external degree-two ports and their selected-degree profile above. -/
theorem graph_class : graph.Colorable 2 ∧
    ∀ v, DegreeCapacity.degree graph v ≤ 3 := by
  have hc : ∀ v : Fin 34, color v < 2 := by decide +kernel
  constructor
  · refine ⟨SimpleGraph.Coloring.mk (fun v => (⟨color v,hc v⟩ : Fin 2)) ?_⟩
    intro v w h he
    exact bipartite v w h (congrArg Fin.val he)
  · intro v
    have h := simple_subcubic.2.2 v
    rw [FiniteMasks.list_count] at h
    change (Finset.univ.filter (graph.Adj v)).card ≤ 3
    convert h using 1 <;> congr 1 <;> ext w <;> simp [graph]

/-- The original twenty-set is a canonical dissociation selection. -/
theorem selection : IsKIndependent graph 2 selectedSet ∧ selectedSet.card = 20 := by
  constructor
  · apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
    intro c hc a ha b hb hca hcb
    exact witness_dissociates c a b (Finset.mem_filter.mp hc).2
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hca hcb
  · have h := witness_cardinality
    rw [FiniteMasks.list_count] at h
    simpa [selectedSet] using h

/-- The precise proposed bound on this displayed module. -/
def claim : Prop := beta graph 2 ≤ 19

/-- The module violates nineteen by an actual twenty-set, independently of
any proposed rule for charging its outside port obligations. -/
theorem result : ¬ claim := by
  have hl : selectedSet.card ≤ beta graph 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,selection.1⟩)
  rw [selection.2] at hl
  unfold claim
  omega

end D5.S3.Combinatorics.Graph.StarForming.HeawoodMultiport
