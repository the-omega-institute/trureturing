/- GID: D5/S3/Geometry/OriginalLabelTwoSum/GraphDataCore
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/GraphDataCore
   mirror-E: none(waiver:original-label-graph-data-core)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Existing GraphData and path-derived Rows, factored unchanged so cut-tree consumers do not import wheel certificates. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Raw
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! SOURCE ONLY. These are the existing GraphData declarations, moved verbatim
from the precedence-selected Graph owner; the paired Graph overlay removes
them there and imports this unique owner. No parallel GraphData is introduced. -/
noncomputable section
open Set Finset SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum

/-- Actual graph/tree presentation. Labels outside ground remain available in
the ambient type but do not pretend to label retained tree edges. -/
structure GraphData (Vertex Label : Type*) [Fintype Label] [DecidableEq Label] where
  graph : SimpleGraph Vertex
  tree : SimpleGraph Vertex
  tree_le : tree ≤ graph
  isTree : tree.IsTree
  ground : Finset Label
  edge : Label → Sym2 Vertex
  tree_edges : ∀ x y, tree.Adj x y ↔ ∃ i ∈ ground, edge i = s(x,y)
  labels_injective : ∀ i ∈ ground, ∀ j ∈ ground, edge i = edge j → i = j
  chords : Type*
  start : chords → Vertex
  finish : chords → Vertex
  chord_adj : ∀ c, graph.Adj (start c) (finish c)
  chord_not_tree : ∀ c, ¬ tree.Adj (start c) (finish c)
  chord_cover : ∀ x y, graph.Adj x y → ¬ tree.Adj x y →
    ∃ c, s(start c,finish c) = s(x,y)

namespace GraphData
variable {Vertex Label : Type*} [Fintype Label] [DecidableEq Label]

def path (g : GraphData Vertex Label) (c : g.chords) :
    g.tree.Walk (g.start c) (g.finish c) :=
  Classical.choose (g.isTree.existsUnique_path (g.start c) (g.finish c))

theorem path_eq (g : GraphData Vertex Label) (c : g.chords)
    (p : g.tree.Walk (g.start c) (g.finish c)) (hp : p.IsPath) : g.path c = p :=
  ((Classical.choose_spec (g.isTree.existsUnique_path (g.start c) (g.finish c))).2 p hp).symm

/-- The fundamental row is the original labels of edges in the actual tree path. -/
def rows (g : GraphData Vertex Label) : Rows Label := by
  classical
  exact {
    ground := g.ground
    chords := g.chords
    row := fun c => g.ground.filter (fun i => g.edge i ∈ (g.path c).edges)
    row_supported := fun _ => Finset.filter_subset _ _ }
end GraphData

end D5.S3.Geometry.OriginalLabelTwoSum
