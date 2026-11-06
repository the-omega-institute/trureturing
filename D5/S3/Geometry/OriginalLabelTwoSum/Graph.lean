/- GID: D5/S3/Geometry/OriginalLabelTwoSum/Graph
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/Graph
   mirror-E: none(waiver:original-label-two-sum-graph)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Star, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Original labelled roots are computed from unique paths in actual star spanning trees for the wheel and K4 seed. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Wheel
import D5.S3.Geometry.OriginalLabelTwoSum.GraphDataCore
import Mathlib.Combinatorics.SimpleGraph.Star

/-! UNCOMPILED. GraphData retains actual original tree edges and proves exact
chord coverage. Its rows are COMPUTED from unique paths. The general edge-2-sum
spanning-tree/path-substitution theorem is NOT asserted in this module. -/
noncomputable section
open Set Finset SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum


namespace Wheel
private def rimEnds (i : Fin 4) : Label × Label :=
  ![(1,2),(2,3),(3,4),(4,1)] i
private def rim : SimpleGraph Label where
  Adj x y := ∃ i : Fin 4, s(x,y) = s((rimEnds i).1,(rimEnds i).2)
  symm := by
    intro x y h
    obtain ⟨i,hi⟩ := h
    exact ⟨i,Sym2.eq_swap.trans hi⟩
  loopless := by
    intro x hx
    obtain ⟨i,hi⟩ := hx
    have : ∀ x : Label, ∀ i : Fin 4,
        s(x,x) ≠ s((rimEnds i).1,(rimEnds i).2) := by decide
    exact this x i hi

/-- Actual hub-star/rim-interface wheel. The marked e is rim edge 1--2, not a
spoke or a coordinate of this right tree. -/
def wheelGraphData : GraphData Label Label where
  graph := SimpleGraph.starGraph 0 ⊔ rim
  tree := SimpleGraph.starGraph 0
  tree_le := le_sup_left
  isTree := SimpleGraph.isTree_starGraph 0
  ground := Y
  edge i := s(0,i)
  tree_edges := by
    intro x y
    rw [SimpleGraph.starGraph_adj]
    exact (by decide : ∀ x y : Label,
      (x ≠ y ∧ (x = 0 ∨ y = 0)) ↔ ∃ i ∈ Y, s(0,i) = s(x,y)) x y
  labels_injective := by decide
  chords := Fin 4
  start i := (rimEnds i).1
  finish i := (rimEnds i).2
  chord_adj := by intro i; right; exact ⟨i,rfl⟩
  chord_not_tree := by
    intro i
    rw [SimpleGraph.starGraph_adj]
    exact (by decide : ∀ i : Fin 4,
      ¬ ((rimEnds i).1 ≠ (rimEnds i).2 ∧
          ((rimEnds i).1 = 0 ∨ (rimEnds i).2 = 0))) i
  chord_cover := by
    intro x y h hn
    rcases h with h | h
    · exact False.elim (hn h)
    · obtain ⟨i,hi⟩ := h
      exact ⟨i,hi.symm⟩

private def rimPath (i : Fin 4) :
    (SimpleGraph.starGraph (0 : Label)).Walk (rimEnds i).1 (rimEnds i).2 :=
  .cons (SimpleGraph.starGraph_center_adj' (by
    exact (by decide : ∀ i : Fin 4, (0 : Label) ≠ (rimEnds i).1) i))
    (.cons (SimpleGraph.starGraph_center_adj (by
      exact (by decide : ∀ i : Fin 4, (0 : Label) ≠ (rimEnds i).2) i)) .nil)

private theorem rimPath_isPath (i : Fin 4) : (rimPath i).IsPath := by
  fin_cases i <;> simp [rimPath,rimEnds,SimpleGraph.Walk.cons_isPath_iff]

/-- These are path-derived rows, not an input equation. -/
theorem fundamental_rows : ∀ i : Fin 4,
    wheelGraphData.rows.row i = ![{1,2},{2,3},{3,4},{4,1}] i := by
  intro i
  have hp := wheelGraphData.path_eq i (rimPath i) (rimPath_isPath i)
  change Y.filter (fun k => s(0,k) ∈ (wheelGraphData.path i).edges) = _
  rw [hp]
  fin_cases i <;> decide

/-- Deleting the ACTUAL interface chord row gives E; the full root is A1. -/
theorem wheelOriginalRoot :
    wheelGraphData.rows.root = A1 ∧ (wheelGraphData.rows.without (0 : Fin 4)).root = E := by
  have hr := fundamental_rows
  constructor
  · apply SetLike.ext
    intro s
    change (∃ i : Fin 4, s ⊆ Y \ wheelGraphData.rows.row i) ↔ s ∈ A1
    simp_rw [hr]
    exact (by decide : ∀ s : Finset Label,
      (∃ i : Fin 4, s ⊆ Y \ (![{1,2},{2,3},{3,4},{4,1}] i)) ↔ s ∈ A1) s
  · apply SetLike.ext
    intro s
    change (∃ i : {i : Fin 4 // i ≠ 0}, s ⊆ Y \ wheelGraphData.rows.row i.1) ↔ s ∈ E
    simp_rw [hr]
    exact (by decide : ∀ s : Finset Label,
      (∃ i : {i : Fin 4 // i ≠ 0},
        s ⊆ Y \ (![{1,2},{2,3},{3,4},{4,1}] i.1)) ↔ s ∈ E) s

/-- The native supplier certificates consume this actual graph-derived root. -/
def wheelGraphCertificate : Certificate wheelGraphData.rows.ground wheelGraphData.rows.root where
  supported := by rw [wheelOriginalRoot.1]; exact certificate.supported
  core := certificate.core
  critical := certificate.critical
  vertex := certificate.vertex
  vertex_mem := certificate.vertex_mem
  core_supported := certificate.core_supported
  critical_supported := certificate.critical_supported
  cells := certificate.cells
  main := certificate.main.cast (congrArg project wheelOriginalRoot.1).symm rfl
  separate := certificate.separate
end Wheel

namespace K4
private abbrev Vertex := Fin 4
private def ends (i : Fin 3) : Vertex × Vertex := ![(1,2),(2,3),(1,3)] i
private def spoke (i : SeedLabel) : Vertex := ⟨i.val+1,by omega⟩

def seedGraphData : GraphData Vertex SeedLabel where
  graph := ⊤
  tree := SimpleGraph.starGraph 0
  tree_le := le_top
  isTree := SimpleGraph.isTree_starGraph 0
  ground := Finset.univ
  edge i := s(0,spoke i)
  tree_edges := by
    intro x y
    rw [SimpleGraph.starGraph_adj]
    exact (by decide : ∀ x y : Vertex,
      (x ≠ y ∧ (x = 0 ∨ y = 0)) ↔
        ∃ i ∈ (Finset.univ : Finset SeedLabel), s(0,spoke i) = s(x,y)) x y
  labels_injective := by decide
  chords := Fin 3
  start i := (ends i).1
  finish i := (ends i).2
  chord_adj := by
    intro i
    exact (by decide : ∀ i : Fin 3, (ends i).1 ≠ (ends i).2) i
  chord_not_tree := by
    intro i
    rw [SimpleGraph.starGraph_adj]
    exact (by decide : ∀ i : Fin 3,
      ¬ ((ends i).1 ≠ (ends i).2 ∧ ((ends i).1 = 0 ∨ (ends i).2 = 0))) i
  chord_cover := by
    intro x y h hn
    rw [SimpleGraph.starGraph_adj] at hn
    exact (by decide : ∀ x y : Vertex, x ≠ y →
      ¬ (x ≠ y ∧ (x = 0 ∨ y = 0)) →
        ∃ i : Fin 3, s((ends i).1,(ends i).2) = s(x,y)) x y h hn

private def chordPath (i : Fin 3) :
    (SimpleGraph.starGraph (0 : Vertex)).Walk (ends i).1 (ends i).2 :=
  .cons (SimpleGraph.starGraph_center_adj' (by
    exact (by decide : ∀ i : Fin 3, (0 : Vertex) ≠ (ends i).1) i))
    (.cons (SimpleGraph.starGraph_center_adj (by
      exact (by decide : ∀ i : Fin 3, (0 : Vertex) ≠ (ends i).2) i)) .nil)

/-- K4's actual star-tree paths compute the seed row root. -/
theorem seedOriginalRoot : seedGraphData.rows.root = root := by
  have hr : ∀ i : Fin 3, seedGraphData.rows.row i = ![{0,1},{1,2},{0,2}] i := by
    intro i
    have hpath : (chordPath i).IsPath := by
      fin_cases i <;> simp [chordPath,ends,SimpleGraph.Walk.cons_isPath_iff]
    have hp := seedGraphData.path_eq i (chordPath i) hpath
    change Finset.univ.filter (fun k => s(0,spoke k) ∈ (seedGraphData.path i).edges) = _
    rw [hp]
    fin_cases i <;> decide
  apply SetLike.ext
  intro s
  change (∃ i : Fin 3, s ⊆ Finset.univ \ seedGraphData.rows.row i) ↔ s ∈ root
  simp_rw [hr]
  exact (by decide : ∀ s : Finset SeedLabel,
    (∃ i : Fin 3, s ⊆ Finset.univ \ (![{0,1},{1,2},{0,2}] i)) ↔ s ∈ root) s

def seedGraphCertificate : Certificate seedGraphData.rows.ground seedGraphData.rows.root where
  supported := by rw [seedOriginalRoot]; exact seed.supported
  core := seed.core
  critical := seed.critical
  vertex := seed.vertex
  vertex_mem := seed.vertex_mem
  core_supported := seed.core_supported
  critical_supported := seed.critical_supported
  cells := seed.cells
  main := seed.main.cast (congrArg project seedOriginalRoot).symm rfl
  separate := seed.separate
end K4
end D5.S3.Geometry.OriginalLabelTwoSum
