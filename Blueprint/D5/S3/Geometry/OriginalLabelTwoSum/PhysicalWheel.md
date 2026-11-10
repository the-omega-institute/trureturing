# PhysicalWheel

## Abstract

Fixed W4 actual physical gluing on arbitrary original ambient labels, retaining all ghosts.

This is the released actual fixed W4 construction on arbitrary original ambient labels, with every additional ghost assigned an explicit total edge value. It preserves the original graph, tree, four chord indices and endpoints. It asserts no arbitrary marking, graph history, native certificate or universal structural supplier.

**Definition 1.1 (ambientEdge).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambientEdge`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambientEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.Wheel.ambientEdge. For an injective f : Label ↪ Ambient, define the total edge at i by the original wheel edge of its unique preimage when one exists, and by the hub loop s(0,0) otherwise. The original nonground zero label also has its prescribed wheel value; extra ambient ghosts are explicitly assigned the loop.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum.Wheel

variable {Ambient VL : Type*} [Fintype Ambient] [DecidableEq Ambient]

Exact source definition:

def ambientEdge (f : Label ↪ Ambient) (i : Ambient) : Sym2 Label :=

  if h : ∃ j : Label, f j = i then wheelGraphData.edge (Classical.choose h) else s(0,0)

**Theorem 1.2 (ambientEdge_image).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambientEdge_image`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambientEdge_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.Wheel.ambientEdge_image. At every original wheel label j, including zero, ambientEdge f (f j) equals wheelGraphData.edge j. The image witness selects a preimage, and f.injective identifies it with j.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum.Wheel

variable {Ambient VL : Type*} [Fintype Ambient] [DecidableEq Ambient]

Exact source statement (proof in the paired Lean module):

theorem ambientEdge_image (f : Label ↪ Ambient) (j : Label) :

    ambientEdge f (f j) = wheelGraphData.edge j

**Definition 1.3 (ambientGraph).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambientGraph`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambientGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.Wheel.ambientGraph. Construct GraphData Label Ambient with the original wheel graph, tree, four chord indices and start/finish endpoints, changing only the label ground to Y.image f and the total edge function to ambientEdge f. Image witnesses and ambientEdge_image prove tree-edge coverage and ground-label injectivity; all original chord proofs are inherited.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum.Wheel

variable {Ambient VL : Type*} [Fintype Ambient] [DecidableEq Ambient]

Exact source definition:

def ambientGraph (f : Label ↪ Ambient) : GraphData Label Ambient where

  graph := wheelGraphData.graph

  tree := wheelGraphData.tree

  tree_le := wheelGraphData.tree_le

  isTree := wheelGraphData.isTree

  ground := Y.image f

  edge := ambientEdge f

  tree_edges := by

    intro x y

    rw [wheelGraphData.tree_edges x y]

    constructor

    · rintro ⟨j,hj,he⟩

      exact ⟨f j,Finset.mem_image.mpr ⟨j,hj,rfl⟩,(ambientEdge_image f j).trans he⟩

    · rintro ⟨i,hi,he⟩

      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi

      exact ⟨j,hj,(ambientEdge_image f j).symm.trans he⟩

  labels_injective := by

    intro i hi j hj he

    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hi

    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj

    rw [ambientEdge_image,ambientEdge_image] at he

    exact congrArg f (wheelGraphData.labels_injective u hu v hv he)

  chords := wheelGraphData.chords

  start := wheelGraphData.start

  finish := wheelGraphData.finish

  chord_adj := wheelGraphData.chord_adj

  chord_not_tree := wheelGraphData.chord_not_tree

  chord_cover := wheelGraphData.chord_cover

**Theorem 1.4 (ambient_row).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_row`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.Wheel.ambient_row. For each original c : Fin 4, the actual ambient path row is the finset image under f of the original wheel row. First identify the chosen tree path with wheelGraphData.path c by path uniqueness, then expand row filtering and use ambientEdge_image. This is an equality of original indexed rows.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum.Wheel

variable {Ambient VL : Type*} [Fintype Ambient] [DecidableEq Ambient]

local instance : OfNat wheelGraphData.chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

local instance (f : Label ↪ Ambient) : OfNat (ambientGraph f).chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

Exact source statement (proof in the paired Lean module):

theorem ambient_row (f : Label ↪ Ambient) (c : Fin 4) :

    (ambientGraph f).rows.row c = (wheelGraphData.rows.row c).image f

**Theorem 1.5 (ambient_uniqueInterface).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_uniqueInterface`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_uniqueInterface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.Wheel.ambient_uniqueInterface. The actual ambient graph has local UniqueInterface at the original index 0 : Fin 4. Its chord starts and finishes are unchanged, so the proof consumes wheel_uniqueInterface directly. This concerns the selected physical fiber only.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum.Wheel

variable {Ambient VL : Type*} [Fintype Ambient] [DecidableEq Ambient]

local instance : OfNat wheelGraphData.chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

local instance (f : Label ↪ Ambient) : OfNat (ambientGraph f).chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

Exact source statement (proof in the paired Lean module):

theorem ambient_uniqueInterface (f : Label ↪ Ambient) :

    (ambientGraph f).UniqueInterface (0 : Fin 4)

**Theorem 1.6 (ambient_E_edge).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_E_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_E_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.Wheel.ambient_E_edge. Physical-fiber deletion at the original index 0 yields renameFamily f E. Extensionality transports every original PhysicalSurvivor complement using ambient_row and injective-image set difference, and then consumes wheel_E_edge. The proof does not infer physical deletion from row equality alone.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum.Wheel

variable {Ambient VL : Type*} [Fintype Ambient] [DecidableEq Ambient]

local instance : OfNat wheelGraphData.chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

local instance (f : Label ↪ Ambient) : OfNat (ambientGraph f).chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

Exact source statement (proof in the paired Lean module):

theorem ambient_E_edge (f : Label ↪ Ambient) :

    (ambientGraph f).E_edge (0 : Fin 4) = renameFamily f E

**Theorem 1.7 (ambient_without).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_without`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_without` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.Wheel.ambient_without. Literal one-index deletion at 0 also has root renameFamily f E. Rewrite it to physical E_edge using the proved ambient_uniqueInterface f and E_edge_eq_without, then apply ambient_E_edge. The local uniqueness step distinguishes this equation from physical deletion.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum.Wheel

variable {Ambient VL : Type*} [Fintype Ambient] [DecidableEq Ambient]

local instance : OfNat wheelGraphData.chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

local instance (f : Label ↪ Ambient) : OfNat (ambientGraph f).chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

Exact source statement (proof in the paired Lean module):

theorem ambient_without (f : Label ↪ Ambient) :

    ((ambientGraph f).rows.without (0 : Fin 4)).root = renameFamily f E

**Theorem 1.8 (zero_outside_ground).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.zero_outside_ground`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.zero_outside_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.Wheel.zero_outside_ground. The prescribed label f 0 lies outside Y.image f. A contrary image witness would equal zero by f.injective, contradicting the original zero ∉ Y. This supplies e-exclusion on the right side of ambientGlue.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum.Wheel

variable {Ambient VL : Type*} [Fintype Ambient] [DecidableEq Ambient]

local instance : OfNat wheelGraphData.chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

local instance (f : Label ↪ Ambient) : OfNat (ambientGraph f).chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

Exact source statement (proof in the paired Lean module):

theorem zero_outside_ground (f : Label ↪ Ambient) : f 0 ∉ Y.image f

**Definition 1.9 (ambientGlue).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambientGlue`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambientGlue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.Wheel.ambientGlue. Given the original left GraphData, ground equation left.ground = insert e X, actual endpoint equation left.edge e = s(a,b), injective f with f 0 = e, e ∉ X and Disjoint X (Y.image f), construct PhysicalGlue with right = ambientGraph f and selected = 0. Right e-exclusion follows from zero_outside_ground; no parent graph/root is supplied by the caller.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum.Wheel

variable {Ambient VL : Type*} [Fintype Ambient] [DecidableEq Ambient]

local instance : OfNat wheelGraphData.chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

local instance (f : Label ↪ Ambient) : OfNat (ambientGraph f).chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

Exact source definition:

def ambientGlue (left : GraphData VL Ambient) (X : Finset Ambient) (e : Ambient)

    (a b : VL) (hleft : left.ground = insert e X) (hedge : left.edge e = s(a,b))

    (f : Label ↪ Ambient) (hf0 : f 0 = e) (heX : e ∉ X)

    (hXY : Disjoint X (Y.image f)) : PhysicalGlue VL Label Ambient where

  left := left

  right := ambientGraph f

  selected := 0

  X := X

  Y := Y.image f

  e := e

  left_ground := hleft

  right_ground := rfl

  e_not_X := heX

  e_not_Y := hf0 ▸ zero_outside_ground f

  disjoint := hXY

  aL := a

  bL := b

  edge_e := hedge

**Theorem 1.10 (ambient_actual_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_actual_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_actual_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.Wheel.ambient_actual_root. For exactly the left data and hypotheses in the statement below, the actual glued graph root equals phi X (Y.image f) (Z.image f) (restrict X left.rows.root) (rawLink X e left.rows.root) (renameFamily f E). Apply the unrestricted PhysicalGlue.root_formula, use ambient_row and fundamental_rows 0 to identify the selected row with R.image f, use injectivity to identify its complement with Z.image f, and consume ambient_E_edge. X and the ambient label type remain original, including all ghosts outside the active union.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum.Wheel

variable {Ambient VL : Type*} [Fintype Ambient] [DecidableEq Ambient]

local instance : OfNat wheelGraphData.chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

local instance (f : Label ↪ Ambient) : OfNat (ambientGraph f).chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

Exact source statement (proof in the paired Lean module):

theorem ambient_actual_root (left : GraphData VL Ambient) (X : Finset Ambient) (e : Ambient)

    (a b : VL) (hleft : left.ground = insert e X) (hedge : left.edge e = s(a,b))

    (f : Label ↪ Ambient) (hf0 : f 0 = e) (heX : e ∉ X)

    (hXY : Disjoint X (Y.image f)) :

    (ambientGlue left X e a b hleft hedge f hf0 heX hXY).data.rows.root =

      phi X (Y.image f) (Z.image f) (restrict X left.rows.root)

        (rawLink X e left.rows.root) (renameFamily f E)

**Theorem 1.11 (ambient_actual_literal_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_actual_literal_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_actual_literal_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D5.S3.Geometry.OriginalLabelTwoSum.Wheel.ambient_actual_literal_root. With the same complete endpoint, ground, injectivity, f 0 = e, e-exclusion and disjointness hypotheses, the last factor is instead the root of the original ambient wheel rows with index 0 removed. Rewrite that factor with ambient_without and consume ambient_actual_root. The fixed wheel supplies its local UniqueInterface proof internally, preserving its three original survivor indices; PhysicalGlue acquires no global chord-injectivity premise.

### Exact source contract

Exact lexical source context (not a compiled telescope):

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum.Wheel

variable {Ambient VL : Type*} [Fintype Ambient] [DecidableEq Ambient]

local instance : OfNat wheelGraphData.chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

local instance (f : Label ↪ Ambient) : OfNat (ambientGraph f).chords 0 :=

  inferInstanceAs (OfNat (Fin 4) 0)

Exact source statement (proof in the paired Lean module):

theorem ambient_actual_literal_root (left : GraphData VL Ambient) (X : Finset Ambient) (e : Ambient)

    (a b : VL) (hleft : left.ground = insert e X) (hedge : left.edge e = s(a,b))

    (f : Label ↪ Ambient) (hf0 : f 0 = e) (heX : e ∉ X)

    (hXY : Disjoint X (Y.image f)) :

    (ambientGlue left X e a b hleft hedge f hf0 heX hXY).data.rows.root =

      phi X (Y.image f) (Z.image f) (restrict X left.rows.root)

        (rawLink X e left.rows.root) ((ambientGraph f).rows.without (0 : Fin 4)).root

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambientEdge`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambientEdge_image`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambientGlue`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambientGraph`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_E_edge`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_actual_literal_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_actual_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_row`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_uniqueInterface`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.ambient_without`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalWheel.zero_outside_ground`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/PhysicalGlue](PhysicalGlue.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Rename](Rename.md)
