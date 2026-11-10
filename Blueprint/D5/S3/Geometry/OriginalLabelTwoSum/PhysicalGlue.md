# PhysicalGlue

## Abstract

Actual physical edge two-sum GraphData and path-derived rows on the unchanged ambient labels.

Original input graphs supply the retained left tree edge and selected right chord. The parent graph and tree, total labels, chord coverage and actual path rows are constructed. Active ground labels remain X ∪ Y on the same ambient Label; other ambient values and duplicate noninterface chord indices are retained. The unrestricted physical-fiber formula and the local-U* literal corollaries have different hypotheses.

**Definition 1.1 (PhysicalGlue).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.PhysicalGlue`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.PhysicalGlue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue. The input structure supplies the two original GraphData values, a selected right chord, disjoint surviving grounds X and Y, the excluded label e, and its actual left endpoints. The chord universes uLeftChord and uRightChord are independent, and VL and VR are arbitrary Type*. Only Label has Fintype and DecidableEq instances. No parent graph, path, row, root, or UniqueInterface assumption is a field.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

Exact source definition:

structure PhysicalGlue (VL VR Label : Type*) [Fintype Label] [DecidableEq Label] where

  left : GraphData.{_, _, uLeftChord} VL Label

  right : GraphData.{_, _, uRightChord} VR Label

  selected : right.chords

  X : Finset Label

  Y : Finset Label

  e : Label

  left_ground : left.ground = insert e X

  right_ground : right.ground = Y

  e_not_X : e ∉ X

  e_not_Y : e ∉ Y

  disjoint : Disjoint X Y

  aL : VL

  bL : VL

  edge_e : left.edge e = s(aL,bL)

**Theorem 1.2 (selected_mem).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.selected_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.selected_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.selected_mem. The selected left label e belongs to left.ground because that ground is insert e X. This supplies the actual retained-edge witness used to construct GraphSource.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem selected_mem : g.e ∈ g.left.ground

**Definition 1.3 (source).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.source`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.source` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.source. Build GraphSource from g.left and g.right, with left terminals aL,bL and right terminals start selected,finish selected. Right-terminal distinctness follows from chord_adj selected, while selected_mem and edge_e supply the original left interface data.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

def source : GraphSource VL VR Label Label where

  left := g.left

  right := g.right

  aL := g.aL

  bL := g.bL

  aR := g.right.start g.selected

  bR := g.right.finish g.selected

  htermR := (g.right.chord_adj g.selected).ne

  e := g.e

  he := g.selected_mem

  edge_e := g.edge_e

**Definition 1.4 (input).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.input`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.input` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.input. Use g.source.input, the existing CutTree input on those actual graph terminals. Its tree and path construction are consumed by the parent graph proofs.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

abbrev input := g.source.input

abbrev Carrier := g.input.Carrier

abbrev qL := g.input.qL

abbrev qR := g.input.qR

abbrev leftKept := g.left.graph.deleteEdges {g.left.edge g.e}

abbrev rightKept := g.right.graph.deleteEdges {g.right.kappa g.selected}

**Definition 1.5 (Carrier).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.Carrier`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.Carrier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.Carrier. The parent vertex type is exactly g.input.Carrier, the carrier supplied by the terminal gluing construction. It changes the vertex carrier while the ambient edge-label type Label stays original.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

abbrev Carrier := g.input.Carrier

abbrev qL := g.input.qL

abbrev qR := g.input.qR

abbrev leftKept := g.left.graph.deleteEdges {g.left.edge g.e}

abbrev rightKept := g.right.graph.deleteEdges {g.right.kappa g.selected}

**Definition 1.6 (qL).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.qL`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.qL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.qL. The left vertex map is exactly g.input.qL. Its injectivity and its overlap with qR are used to identify graph adjacency and exclude cross-image collisions.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

abbrev qL := g.input.qL

abbrev qR := g.input.qR

abbrev leftKept := g.left.graph.deleteEdges {g.left.edge g.e}

abbrev rightKept := g.right.graph.deleteEdges {g.right.kappa g.selected}

**Definition 1.7 (qR).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.qR`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.qR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.qR. The right vertex map is exactly g.input.qR. Right chord endpoints and retained physical edges are transported by this map.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

abbrev qR := g.input.qR

abbrev leftKept := g.left.graph.deleteEdges {g.left.edge g.e}

abbrev rightKept := g.right.graph.deleteEdges {g.right.kappa g.selected}

**Definition 1.8 (leftKept).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.leftKept`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.leftKept` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.leftKept. Delete the singleton physical edge left.edge e from the original left graph. This deletion is used before mapping the graph into the glued carrier.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

abbrev leftKept := g.left.graph.deleteEdges {g.left.edge g.e}

abbrev rightKept := g.right.graph.deleteEdges {g.right.kappa g.selected}

**Definition 1.9 (rightKept).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.rightKept`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.rightKept` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.rightKept. Delete the singleton unordered physical chord right.kappa selected from the original right graph. Every index for that same physical interface is thereby excluded from the surviving chord type.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

abbrev rightKept := g.right.graph.deleteEdges {g.right.kappa g.selected}

**Definition 1.10 (graph).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.graph. The actual parent graph is the supremum of the two retained graph images, using the input leftEmbedding and rightEmbedding. Both physical interface edges are deleted before taking this union.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

def graph : SimpleGraph g.Carrier :=

  g.leftKept.map g.input.leftEmbedding ⊔ g.rightKept.map g.input.rightEmbedding

**Theorem 1.11 (graph_adjacency).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_adjacency`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_adjacency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.graph_adjacency. Expand graph supremum and graph-map adjacency: a parent adjacency has witnesses in either retained input graph, with their two endpoints mapped to w and z. Conversely either such witnessed adjacency lies in the parent.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem graph_adjacency (w z : g.Carrier) : g.graph.Adj w z ↔

    (∃ x y, g.leftKept.Adj x y ∧ g.qL x = w ∧ g.qL y = z) ∨

    (∃ x y, g.rightKept.Adj x y ∧ g.qR x = w ∧ g.qR y = z)

**Theorem 1.12 (graph_edgeSet).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_edgeSet`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_edgeSet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.graph_edgeSet. Expand the edge set of the graph supremum and each graph map. The result is precisely the union of the qL-image of leftKept.edgeSet and the qR-image of rightKept.edgeSet.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem graph_edgeSet : g.graph.edgeSet =

    Sym2.map g.qL '' g.leftKept.edgeSet ∪

      Sym2.map g.qR '' g.rightKept.edgeSet

**Theorem 1.13 (cross_pair).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.cross_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.cross_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.cross_pair. For x ≠ y, an equality between the two mapped unordered pairs forces the original left pair to be the left terminal pair and the original right pair to be the selected physical chord. The proof treats aligned and reversed endpoints using input.overlap; it makes no claim about ghost-label loops.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem cross_pair {x y : VL} {u v : VR} (hne : x ≠ y)

    (he : Sym2.map g.qL s(x,y) = Sym2.map g.qR s(u,v)) :

    s(x,y) = s(g.aL,g.bL) ∧ s(u,v) = g.right.kappa g.selected

**Theorem 1.14 (graph_images_disjoint).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_images_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_images_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.graph_images_disjoint. The two retained physical edge images are disjoint. Any common edge would be a nonloop adjacency whose cross_pair identity is exactly a deleted interface edge, contradicting retained membership. Duplicate indices on other right physical edges remain available.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem graph_images_disjoint :

    Disjoint (Sym2.map g.qL '' g.leftKept.edgeSet)

      (Sym2.map g.qR '' g.rightKept.edgeSet)

**Theorem 1.15 (graph_left).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_left`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.graph_left. Pulling parent adjacency back along qL recovers exactly leftKept adjacency. Injectivity handles a left witness; cross_pair excludes a right witness because its physical interface edge has been deleted.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem graph_left (x y : VL) :

    g.graph.Adj (g.qL x) (g.qL y) ↔ g.leftKept.Adj x y

**Theorem 1.16 (graph_right).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_right`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.graph_right. Pulling parent adjacency back along qR recovers exactly rightKept adjacency. Injectivity handles a right witness; cross_pair excludes a left witness on the deleted left interface.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem graph_right (x y : VR) :

    g.graph.Adj (g.qR x) (g.qR y) ↔ g.rightKept.Adj x y

**Theorem 1.17 (tree_left).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.tree_left`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.tree_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.tree_left. The constructed input tree restricted along qL is exactly the cut left tree. The extra right-terminal adjacency alternative disappears by chord_not_tree for the selected right chord.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem tree_left (x y : VL) :

    g.input.tree.Adj (g.qL x) (g.qL y) ↔ g.input.cut.Adj x y

**Theorem 1.18 (tree_le).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.tree_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.tree_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.tree_le. Every edge of the constructed input tree belongs to the actual parent graph. Left cut edges survive left graph deletion; right tree edges survive deletion of the selected nontree chord, so both alternatives embed into graph.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem tree_le : g.input.tree ≤ g.graph

**Definition 1.19 (labelEdge).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.labelEdge`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.labelEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.labelEdge. Define a total edge function on every original Label: use the mapped right edge when i ∈ Y, and the mapped left edge otherwise. Thus e and all labels outside the active ground still have prescribed values.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

def labelEdge (i : Label) : Sym2 g.Carrier :=

  if i ∈ g.Y then Sym2.map g.qR (g.right.edge i)

  else Sym2.map g.qL (g.left.edge i)

**Theorem 1.20 (label_left).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.label_left`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.label_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.label_left. For i ∈ X, disjointness of X and Y forces i ∉ Y, so the total label function selects exactly the mapped original left edge.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem label_left {i : Label} (hi : i ∈ g.X) :

    g.labelEdge i = Sym2.map g.qL (g.left.edge i)

**Theorem 1.21 (label_right).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.label_right`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.label_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.label_right. For i ∈ Y, the total label function selects exactly the mapped original right edge by its defining positive branch.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem label_right {i : Label} (hi : i ∈ g.Y) :

    g.labelEdge i = Sym2.map g.qR (g.right.edge i)

**Theorem 1.22 (retained_label_mem).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.retained_label_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.retained_label_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.retained_label_mem. An original left label in X labels an edge of the cut input tree. It first labels an original tree edge; equality with the removed edge would force i = e by the original ground-label injectivity, contrary to e_not_X.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem retained_label_mem {i : Label} (hi : i ∈ g.X) :

    g.left.edge i ∈ g.input.cut.edgeSet

**Theorem 1.23 (active_label_mem).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.active_label_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.active_label_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.active_label_mem. Every label in X ∪ Y labels an actual constructed tree edge. Split the union membership: use retained_label_mem on X and the original right tree-edge property on Y, then the input edge-set union.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem active_label_mem {i : Label} (hi : i ∈ g.X ∪ g.Y) :

    g.labelEdge i ∈ g.input.tree.edgeSet

**Theorem 1.24 (tree_edges).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.tree_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.tree_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.tree_edges. The input tree adjacency is equivalent to existence of an active original label i ∈ X ∪ Y with labelEdge i = s(w,z). Forward direction extracts the original tree label from either input branch; reverse direction consumes active_label_mem.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem tree_edges (w z : g.Carrier) :

    g.input.tree.Adj w z ↔ ∃ i ∈ g.X ∪ g.Y, g.labelEdge i = s(w,z)

**Theorem 1.25 (labels_injective).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.labels_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.labels_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.labels_injective. The total label function is injective on the active ground X ∪ Y. Within each side, use the original labels_injective and the vertex-map injectivity; across sides, use the disjoint tree-edge images. No injectivity is imposed on ghost labels or on all chord indices.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem labels_injective (i : Label) (hi : i ∈ g.X ∪ g.Y)

    (j : Label) (hj : j ∈ g.X ∪ g.Y) (he : g.labelEdge i = g.labelEdge j) : i = j

**Definition 1.26 (Chords).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.Chords`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.Chords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.Chords. The parent chord type is the sum of every original left index and every original right PhysicalSurvivor of selected. PhysicalSurvivor means kappa d ≠ kappa selected; other duplicate fibers are retained without quotienting.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

abbrev Chords := g.left.chords ⊕ g.right.PhysicalSurvivor g.selected

**Definition 1.27 (start).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.start`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.start` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.start. Define parent chord starts by cases on Chords: map left.start c through qL, and right.start d.1 through qR for a physical survivor d.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

def start : g.Chords → g.Carrier

  | .inl c => g.qL (g.left.start c)

  | .inr d => g.qR (g.right.start d.1)

**Definition 1.28 (finish).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.finish`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.finish` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.finish. Define parent chord finishes by the same original sum indices: map left.finish c through qL, and right.finish d.1 through qR.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

def finish : g.Chords → g.Carrier

  | .inl c => g.qL (g.left.finish c)

  | .inr d => g.qR (g.right.finish d.1)

**Theorem 1.29 (chord_adj).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.chord_adj`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.chord_adj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.chord_adj. Every constructed chord is an adjacency in the actual parent graph. A left chord cannot equal the removed left tree edge because it is nontree; a right PhysicalSurvivor explicitly differs from the removed right physical edge.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem chord_adj (c : g.Chords) : g.graph.Adj (g.start c) (g.finish c)

**Theorem 1.30 (chord_not_tree).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.chord_not_tree`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.chord_not_tree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.chord_not_tree. No constructed chord lies in the constructed input tree. Pull a left chord back through tree_left to the original left tree, or a right chord through adjacency_right to the original right tree, and apply its original chord_not_tree proof.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem chord_not_tree (c : g.Chords) :

    ¬g.input.tree.Adj (g.start c) (g.finish c)

**Theorem 1.31 (chord_cover).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.chord_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.chord_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.chord_cover. Every parent graph edge outside the constructed tree is covered by a constructed chord. Split graph adjacency by side, obtain an original nontree chord using that side's chord_cover, and for the right branch derive physical-survivor evidence from the retained-edge deletion.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem chord_cover (w z : g.Carrier) (h : g.graph.Adj w z)

    (hn : ¬g.input.tree.Adj w z) : ∃ c : g.Chords, s(g.start c,g.finish c) = s(w,z)

**Definition 1.32 (data).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.data`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.data` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.data. Assemble the parent GraphData from graph, input.tree, the proved tree inclusion, source.actual_tree, ground X ∪ Y, total labelEdge, and all proved label/chord properties. The defining assignments below show each field's construction; none is supplied as a desired parent conclusion.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

def data : GraphData g.Carrier Label where

  graph := g.graph

  tree := g.input.tree

  tree_le := g.tree_le

  isTree := g.source.actual_tree

  ground := g.X ∪ g.Y

  edge := g.labelEdge

  tree_edges := g.tree_edges

  labels_injective := g.labels_injective

  chords := g.Chords

  start := g.start

  finish := g.finish

  chord_adj := g.chord_adj

  chord_not_tree := g.chord_not_tree

  chord_cover := g.chord_cover

**Theorem 1.33 (left_row).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.left_row`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.left_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.left_row. The actual parent row at inl c is exactly substitute e (right.rows.row selected) (left.rows.row c). The proof transports the actual oriented path row through tagged_left and source.left_row_of_interface, then forgets tags. It splits whether e lies in the original left row; both orientations, zero-length path segments and duplicate original indices are retained.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem left_row (c : g.left.chords) :

    g.data.rows.row (.inl c) = substitute g.e (g.right.rows.row g.selected) (g.left.rows.row c)

**Theorem 1.34 (right_row).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.right_row`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.right_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.right_row. The actual parent row at a right PhysicalSurvivor d is literally right.rows.row d.1. The proof uses tagged_right and source.right_row_inheritance, then simplifies the image of the original row under the identity map.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem right_row (d : g.right.PhysicalSurvivor g.selected) :

    g.data.rows.row (.inr d) = g.right.rows.row d.1

**Theorem 1.35 (row_family).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.row_family`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.row_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.row_family. At each original parent chord index c, the actual path-derived row equals the corresponding physicalTransportedRows row. Case analysis uses left_row or right_row, with no quotient or assumed row identity in the input structure.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem row_family (c : g.data.chords) : g.data.rows.row c =

    (physicalTransportedRows g.X g.Y g.e g.left.rows g.right g.selected

      g.left_ground g.right_ground g.e_not_X g.e_not_Y).row c

**Theorem 1.36 (root_agreement).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.root_agreement`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.root_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.root_agreement. The actual parent complement root equals the root of physicalTransportedRows on X ∪ Y. Extensionality retains the same existential chord witness in each direction and rewrites its row by row_family; empty chord families and empty complementary faces are preserved.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem root_agreement : g.data.rows.root =

    (physicalTransportedRows g.X g.Y g.e g.left.rows g.right g.selected

      g.left_ground g.right_ground g.e_not_X g.e_not_Y).root

**Theorem 1.37 (root_formula).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.root_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.root_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.root_formula. Without any UniqueInterface hypothesis, rewrite root_agreement and apply physical_row_transport. The final factor is right.E_edge selected, whose physical deletion removes the whole selected kappa fiber. The phi formula retains restriction on X, rawLink at e, the selected-row complement in Y, and all VOID/UNIT cases.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem root_formula : g.data.rows.root =

    phi g.X g.Y (g.Y \ g.right.rows.row g.selected) (restrict g.X g.left.rows.root)

      (rawLink g.X g.e g.left.rows.root) (g.right.E_edge g.selected)

**Theorem 1.38 (root_formula_of_unique).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.root_formula_of_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.root_formula_of_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.root_formula_of_unique. Assume only the local hypothesis hu : right.UniqueInterface selected, meaning ∀ d, right.kappa d = right.kappa selected → d = selected. Rewrite the unrestricted root_formula with E_edge_eq_without to replace physical-fiber deletion by the literal one-index root. No uniqueness on other chord fibers is required, and this is no necessity claim for accidental face-set equality.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem root_formula_of_unique (hu : g.right.UniqueInterface g.selected) :

    g.data.rows.root =

      phi g.X g.Y (g.Y \ g.right.rows.row g.selected) (restrict g.X g.left.rows.root)

        (rawLink g.X g.e g.left.rows.root) (g.right.rows.without g.selected).root

**Definition 1.39 (uniqueChordEquiv).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.uniqueChordEquiv`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.uniqueChordEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.uniqueChordEquiv. Under the same local UniqueInterface hypothesis, construct an equivalence from the actual parent indices to the sum of original left indices and right indices d ≠ selected. It is identity on the underlying indices in both directions; hu supplies precisely the converse survivor evidence and preserves duplicate noninterface chords.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source definition:

def uniqueChordEquiv (hu : g.right.UniqueInterface g.selected) :

    g.data.chords ≃ g.left.chords ⊕ {d : g.right.chords // d ≠ g.selected} :=

  Equiv.sumCongr (Equiv.refl _) {

    toFun := fun d => ⟨d.1,fun he => d.2 (congrArg g.right.kappa he)⟩

    invFun := fun d => ⟨d.1,fun he => d.2 (hu d.1 he)⟩

    left_inv := fun d => by apply Subtype.ext; rfl

    right_inv := fun d => by apply Subtype.ext; rfl }

**Theorem 1.40 (unique_row).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.unique_row`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.unique_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.unique_row. Under hu, the actual parent row at c equals the literal transportedRows row at uniqueChordEquiv hu c. Split the sum index and apply left_row or right_row. The selected row's support proof is inherited from the original right ground.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem unique_row (hu : g.right.UniqueInterface g.selected) (c : g.data.chords) :

    g.data.rows.row c =

      (transportedRows g.X g.Y g.e (g.right.rows.row g.selected) g.left.rows g.right.rows

        g.selected g.left_ground g.right_ground g.e_not_X g.e_not_Y

        (g.right_ground ▸ g.right.rows.row_supported g.selected)).row

          (g.uniqueChordEquiv hu c)

**Theorem 1.41 (literal_root_agreement).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.literal_root_agreement`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.literal_root_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue.literal_root_agreement. Under the explicit local UniqueInterface hypothesis, the actual parent root equals the root of literal transportedRows with only selected removed. Compose root_formula_of_unique with the symmetric original row_transport equation, using the selected row's inherited support; the equality retains raw empty-face membership.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum

universe uLeftChord uRightChord

namespace PhysicalGlue

variable {VL VR Label : Type*} [Fintype Label] [DecidableEq Label]

  (g : PhysicalGlue VL VR Label)

Exact source statement (proof in the paired Lean module):

theorem literal_root_agreement (hu : g.right.UniqueInterface g.selected) :

    g.data.rows.root =

      (transportedRows g.X g.Y g.e (g.right.rows.row g.selected) g.left.rows g.right.rows

        g.selected g.left_ground g.right_ground g.e_not_X g.e_not_Y

        (g.right_ground ▸ g.right.rows.row_supported g.selected)).root

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.Carrier`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.Chords`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.PhysicalGlue`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.active_label_mem`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.chord_adj`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.chord_cover`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.chord_not_tree`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.cross_pair`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.data`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.finish`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_adjacency`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_edgeSet`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_images_disjoint`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_left`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.graph_right`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.input`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.labelEdge`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.label_left`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.label_right`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.labels_injective`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.leftKept`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.left_row`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.literal_root_agreement`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.qL`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.qR`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.retained_label_mem`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.rightKept`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.right_row`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.root_agreement`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.root_formula`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.root_formula_of_unique`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.row_family`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.selected_mem`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.source`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.start`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.tree_edges`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.tree_le`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.tree_left`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.uniqueChordEquiv`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue.unique_row`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/CutGraphRows](CutGraphRows.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/InterfaceNormalization](InterfaceNormalization.md)
