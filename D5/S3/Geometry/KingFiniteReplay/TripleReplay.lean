/- GID: D5/S3/Geometry/KingFiniteReplay/TripleReplay
   generality: I
   mirror-B: D5/B/S3/Geometry/KingFiniteReplay/TripleReplay
   mirror-E: none(waiver:finite-graph-singular-homology)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Subgraph]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Geometry/KingFiniteReplay.fortyMoves; premises=D5/S3/Geometry/KingFiniteReplay/TripleReplay.initialAdjacency
   digest: The original seed labels and ten literal triple subdivisions. -/
import D5.S3.Geometry.KingFiniteReplay.DataTriples
import D5.S3.Geometry.IndependenceComplexTorsionSeed

/-! The first ten literal operations on graph-construction.json, SHA-256
ff9876310835eca475074719e41da20ea0d5056d76b996c3ea7d5b63fcaa0980,
are triple subdivisions of the original graph6-complement seed. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace D5.S3.Geometry.KingFiniteReplay
open FiniteGraphSuspensionMoves

/-- The actual Fin 11 seed labels, identified with the certificate's initial
Nat labels by an equivalence whose forward map is exactly Fin.val. -/
def initialLabels : IndependenceComplexTorsionSeed.Vertex ≃ Vertex00 :=
  Equiv.ofBijective (fun x => ⟨x.val, by
    have h : ∀ z : IndependenceComplexTorsionSeed.Vertex, z.val ∈ vertices00 := by decide
    exact h x⟩) ⟨by
    intro x y h
    exact Fin.ext (congrArg Subtype.val h), by
    intro y
    have hy : y.val < 11 := by
      have h : ∀ z : Vertex00, z.val < 11 := by decide
      exact h y
    exact ⟨⟨y.val, hy⟩, Subtype.ext rfl⟩⟩

/-- Adjacency identity with H.compl, computed from the supplier's actual
graph6 decoder and the preserved initial edge list. It is used in step 0. -/
theorem initialAdjacency : ∀ x y : IndependenceComplexTorsionSeed.Vertex,
    graph00.Adj (initialLabels x) (initialLabels y) ↔ IndependenceComplexTorsionSeed.G0.Adj x y := by decide

theorem initialGraphIdentity : IndependenceComplexTorsionSeed.G0.map initialLabels = graph00 :=
  map_eq_of_forward IndependenceComplexTorsionSeed.G0 graph00 initialLabels initialAdjacency

def chain00 : MoveChain IndependenceComplexTorsionSeed.G0 IndependenceComplexTorsionSeed.G0 0 := MoveChain.refl IndependenceComplexTorsionSeed.G0

/- Certificate operation 0 (0-based): triple_subdivision. -/
def a00 : IndependenceComplexTorsionSeed.Vertex := 0
def b00 : IndependenceComplexTorsionSeed.Vertex := 5
theorem edge00 : IndependenceComplexTorsionSeed.G0.Adj a00 b00 := (initialAdjacency _ _).mp (by decide)
def oldLabel00 : (IndependenceComplexTorsionSeed.Vertex) → ℕ := fun x => x.val
def newLabel00 : Fin 3 → ℕ := ![11, 12, 13]
theorem newLabel00_injective : Function.Injective newLabel00 := by decide
theorem fresh00 : ∀ o : IndependenceComplexTorsionSeed.Vertex, ∀ a : Fin 3, oldLabel00 o ≠ newLabel00 a := by decide
theorem labels00_mem : ∀ a : (IndependenceComplexTorsionSeed.Vertex) ⊕ (Fin 3),
    Sum.elim oldLabel00 newLabel00 a ∈ vertices01 := by decide
theorem labels00_cover : ∀ t : Vertex01, ∃ a : (IndependenceComplexTorsionSeed.Vertex) ⊕ (Fin 3),
    Sum.elim oldLabel00 newLabel00 a = t.val := by decide
def labels00 : ((IndependenceComplexTorsionSeed.Vertex) ⊕ (Fin 3)) ≃ Vertex01 :=
  sumLabels vertices01 oldLabel00 newLabel00 (Fin.val_injective)
    newLabel00_injective fresh00 labels00_mem labels00_cover
theorem adjacency00 : ∀ x y : (IndependenceComplexTorsionSeed.Vertex) ⊕ (Fin 3),
    graph01.Adj (labels00 x) (labels00 y) ↔ (tripleSubdivision IndependenceComplexTorsionSeed.G0 a00 b00).Adj x y := by decide
theorem mappedGraph00 : (tripleSubdivision IndependenceComplexTorsionSeed.G0 a00 b00).map labels00 = graph01 :=
  map_eq_of_forward (tripleSubdivision IndependenceComplexTorsionSeed.G0 a00 b00) graph01 labels00 adjacency00
def chain01 : MoveChain IndependenceComplexTorsionSeed.G0 graph01 1 := by
  simpa only [mappedGraph00] using (MoveChain.triple chain00 a00 b00 edge00 labels00)

/- Certificate operation 1 (0-based): triple_subdivision. -/
def a01 : Vertex01 := ⟨13, by decide⟩
def b01 : Vertex01 := ⟨5, by decide⟩
theorem edge01 : graph01.Adj a01 b01 := by decide
def oldLabel01 : (Vertex01) → ℕ := fun x => x.val
def newLabel01 : Fin 3 → ℕ := ![14, 15, 16]
theorem newLabel01_injective : Function.Injective newLabel01 := by decide
theorem fresh01 : ∀ o : Vertex01, ∀ a : Fin 3, oldLabel01 o ≠ newLabel01 a := by decide
theorem labels01_mem : ∀ a : (Vertex01) ⊕ (Fin 3),
    Sum.elim oldLabel01 newLabel01 a ∈ vertices02 := by decide
theorem labels01_cover : ∀ t : Vertex02, ∃ a : (Vertex01) ⊕ (Fin 3),
    Sum.elim oldLabel01 newLabel01 a = t.val := by decide
def labels01 : ((Vertex01) ⊕ (Fin 3)) ≃ Vertex02 :=
  sumLabels vertices02 oldLabel01 newLabel01 (Subtype.val_injective)
    newLabel01_injective fresh01 labels01_mem labels01_cover
theorem adjacency01 : ∀ x y : (Vertex01) ⊕ (Fin 3),
    graph02.Adj (labels01 x) (labels01 y) ↔ (tripleSubdivision graph01 a01 b01).Adj x y := by decide
theorem mappedGraph01 : (tripleSubdivision graph01 a01 b01).map labels01 = graph02 :=
  map_eq_of_forward (tripleSubdivision graph01 a01 b01) graph02 labels01 adjacency01
def chain02 : MoveChain IndependenceComplexTorsionSeed.G0 graph02 2 := by
  simpa only [mappedGraph01] using (MoveChain.triple chain01 a01 b01 edge01 labels01)

/- Certificate operation 2 (0-based): triple_subdivision. -/
def a02 : Vertex02 := ⟨16, by decide⟩
def b02 : Vertex02 := ⟨5, by decide⟩
theorem edge02 : graph02.Adj a02 b02 := by decide
def oldLabel02 : (Vertex02) → ℕ := fun x => x.val
def newLabel02 : Fin 3 → ℕ := ![17, 18, 19]
theorem newLabel02_injective : Function.Injective newLabel02 := by decide
theorem fresh02 : ∀ o : Vertex02, ∀ a : Fin 3, oldLabel02 o ≠ newLabel02 a := by decide
theorem labels02_mem : ∀ a : (Vertex02) ⊕ (Fin 3),
    Sum.elim oldLabel02 newLabel02 a ∈ vertices03 := by decide
theorem labels02_cover : ∀ t : Vertex03, ∃ a : (Vertex02) ⊕ (Fin 3),
    Sum.elim oldLabel02 newLabel02 a = t.val := by decide
def labels02 : ((Vertex02) ⊕ (Fin 3)) ≃ Vertex03 :=
  sumLabels vertices03 oldLabel02 newLabel02 (Subtype.val_injective)
    newLabel02_injective fresh02 labels02_mem labels02_cover
theorem adjacency02 : ∀ x y : (Vertex02) ⊕ (Fin 3),
    graph03.Adj (labels02 x) (labels02 y) ↔ (tripleSubdivision graph02 a02 b02).Adj x y := by decide
theorem mappedGraph02 : (tripleSubdivision graph02 a02 b02).map labels02 = graph03 :=
  map_eq_of_forward (tripleSubdivision graph02 a02 b02) graph03 labels02 adjacency02
def chain03 : MoveChain IndependenceComplexTorsionSeed.G0 graph03 3 := by
  simpa only [mappedGraph02] using (MoveChain.triple chain02 a02 b02 edge02 labels02)

/- Certificate operation 3 (0-based): triple_subdivision. -/
def a03 : Vertex03 := ⟨1, by decide⟩
def b03 : Vertex03 := ⟨4, by decide⟩
theorem edge03 : graph03.Adj a03 b03 := by decide
def oldLabel03 : (Vertex03) → ℕ := fun x => x.val
def newLabel03 : Fin 3 → ℕ := ![20, 21, 22]
theorem newLabel03_injective : Function.Injective newLabel03 := by decide
theorem fresh03 : ∀ o : Vertex03, ∀ a : Fin 3, oldLabel03 o ≠ newLabel03 a := by decide
theorem labels03_mem : ∀ a : (Vertex03) ⊕ (Fin 3),
    Sum.elim oldLabel03 newLabel03 a ∈ vertices04 := by decide
theorem labels03_cover : ∀ t : Vertex04, ∃ a : (Vertex03) ⊕ (Fin 3),
    Sum.elim oldLabel03 newLabel03 a = t.val := by decide
def labels03 : ((Vertex03) ⊕ (Fin 3)) ≃ Vertex04 :=
  sumLabels vertices04 oldLabel03 newLabel03 (Subtype.val_injective)
    newLabel03_injective fresh03 labels03_mem labels03_cover
theorem adjacency03 : ∀ x y : (Vertex03) ⊕ (Fin 3),
    graph04.Adj (labels03 x) (labels03 y) ↔ (tripleSubdivision graph03 a03 b03).Adj x y := by decide
theorem mappedGraph03 : (tripleSubdivision graph03 a03 b03).map labels03 = graph04 :=
  map_eq_of_forward (tripleSubdivision graph03 a03 b03) graph04 labels03 adjacency03
def chain04 : MoveChain IndependenceComplexTorsionSeed.G0 graph04 4 := by
  simpa only [mappedGraph03] using (MoveChain.triple chain03 a03 b03 edge03 labels03)

/- Certificate operation 4 (0-based): triple_subdivision. -/
def a04 : Vertex04 := ⟨1, by decide⟩
def b04 : Vertex04 := ⟨7, by decide⟩
theorem edge04 : graph04.Adj a04 b04 := by decide
def oldLabel04 : (Vertex04) → ℕ := fun x => x.val
def newLabel04 : Fin 3 → ℕ := ![23, 24, 25]
theorem newLabel04_injective : Function.Injective newLabel04 := by decide
theorem fresh04 : ∀ o : Vertex04, ∀ a : Fin 3, oldLabel04 o ≠ newLabel04 a := by decide
theorem labels04_mem : ∀ a : (Vertex04) ⊕ (Fin 3),
    Sum.elim oldLabel04 newLabel04 a ∈ vertices05 := by decide
theorem labels04_cover : ∀ t : Vertex05, ∃ a : (Vertex04) ⊕ (Fin 3),
    Sum.elim oldLabel04 newLabel04 a = t.val := by decide
def labels04 : ((Vertex04) ⊕ (Fin 3)) ≃ Vertex05 :=
  sumLabels vertices05 oldLabel04 newLabel04 (Subtype.val_injective)
    newLabel04_injective fresh04 labels04_mem labels04_cover
theorem adjacency04 : ∀ x y : (Vertex04) ⊕ (Fin 3),
    graph05.Adj (labels04 x) (labels04 y) ↔ (tripleSubdivision graph04 a04 b04).Adj x y := by decide
theorem mappedGraph04 : (tripleSubdivision graph04 a04 b04).map labels04 = graph05 :=
  map_eq_of_forward (tripleSubdivision graph04 a04 b04) graph05 labels04 adjacency04
def chain05 : MoveChain IndependenceComplexTorsionSeed.G0 graph05 5 := by
  simpa only [mappedGraph04] using (MoveChain.triple chain04 a04 b04 edge04 labels04)

/- Certificate operation 5 (0-based): triple_subdivision. -/
def a05 : Vertex05 := ⟨3, by decide⟩
def b05 : Vertex05 := ⟨4, by decide⟩
theorem edge05 : graph05.Adj a05 b05 := by decide
def oldLabel05 : (Vertex05) → ℕ := fun x => x.val
def newLabel05 : Fin 3 → ℕ := ![26, 27, 28]
theorem newLabel05_injective : Function.Injective newLabel05 := by decide
theorem fresh05 : ∀ o : Vertex05, ∀ a : Fin 3, oldLabel05 o ≠ newLabel05 a := by decide
theorem labels05_mem : ∀ a : (Vertex05) ⊕ (Fin 3),
    Sum.elim oldLabel05 newLabel05 a ∈ vertices06 := by decide
theorem labels05_cover : ∀ t : Vertex06, ∃ a : (Vertex05) ⊕ (Fin 3),
    Sum.elim oldLabel05 newLabel05 a = t.val := by decide
def labels05 : ((Vertex05) ⊕ (Fin 3)) ≃ Vertex06 :=
  sumLabels vertices06 oldLabel05 newLabel05 (Subtype.val_injective)
    newLabel05_injective fresh05 labels05_mem labels05_cover
theorem adjacency05 : ∀ x y : (Vertex05) ⊕ (Fin 3),
    graph06.Adj (labels05 x) (labels05 y) ↔ (tripleSubdivision graph05 a05 b05).Adj x y := by decide
theorem mappedGraph05 : (tripleSubdivision graph05 a05 b05).map labels05 = graph06 :=
  map_eq_of_forward (tripleSubdivision graph05 a05 b05) graph06 labels05 adjacency05
def chain06 : MoveChain IndependenceComplexTorsionSeed.G0 graph06 6 := by
  simpa only [mappedGraph05] using (MoveChain.triple chain05 a05 b05 edge05 labels05)

/- Certificate operation 6 (0-based): triple_subdivision. -/
def a06 : Vertex06 := ⟨4, by decide⟩
def b06 : Vertex06 := ⟨10, by decide⟩
theorem edge06 : graph06.Adj a06 b06 := by decide
def oldLabel06 : (Vertex06) → ℕ := fun x => x.val
def newLabel06 : Fin 3 → ℕ := ![29, 30, 31]
theorem newLabel06_injective : Function.Injective newLabel06 := by decide
theorem fresh06 : ∀ o : Vertex06, ∀ a : Fin 3, oldLabel06 o ≠ newLabel06 a := by decide
theorem labels06_mem : ∀ a : (Vertex06) ⊕ (Fin 3),
    Sum.elim oldLabel06 newLabel06 a ∈ vertices07 := by decide
theorem labels06_cover : ∀ t : Vertex07, ∃ a : (Vertex06) ⊕ (Fin 3),
    Sum.elim oldLabel06 newLabel06 a = t.val := by decide
def labels06 : ((Vertex06) ⊕ (Fin 3)) ≃ Vertex07 :=
  sumLabels vertices07 oldLabel06 newLabel06 (Subtype.val_injective)
    newLabel06_injective fresh06 labels06_mem labels06_cover
theorem adjacency06 : ∀ x y : (Vertex06) ⊕ (Fin 3),
    graph07.Adj (labels06 x) (labels06 y) ↔ (tripleSubdivision graph06 a06 b06).Adj x y := by decide
theorem mappedGraph06 : (tripleSubdivision graph06 a06 b06).map labels06 = graph07 :=
  map_eq_of_forward (tripleSubdivision graph06 a06 b06) graph07 labels06 adjacency06
def chain07 : MoveChain IndependenceComplexTorsionSeed.G0 graph07 7 := by
  simpa only [mappedGraph06] using (MoveChain.triple chain06 a06 b06 edge06 labels06)

/- Certificate operation 7 (0-based): triple_subdivision. -/
def a07 : Vertex07 := ⟨5, by decide⟩
def b07 : Vertex07 := ⟨6, by decide⟩
theorem edge07 : graph07.Adj a07 b07 := by decide
def oldLabel07 : (Vertex07) → ℕ := fun x => x.val
def newLabel07 : Fin 3 → ℕ := ![32, 33, 34]
theorem newLabel07_injective : Function.Injective newLabel07 := by decide
theorem fresh07 : ∀ o : Vertex07, ∀ a : Fin 3, oldLabel07 o ≠ newLabel07 a := by decide
theorem labels07_mem : ∀ a : (Vertex07) ⊕ (Fin 3),
    Sum.elim oldLabel07 newLabel07 a ∈ vertices08 := by decide
theorem labels07_cover : ∀ t : Vertex08, ∃ a : (Vertex07) ⊕ (Fin 3),
    Sum.elim oldLabel07 newLabel07 a = t.val := by decide
def labels07 : ((Vertex07) ⊕ (Fin 3)) ≃ Vertex08 :=
  sumLabels vertices08 oldLabel07 newLabel07 (Subtype.val_injective)
    newLabel07_injective fresh07 labels07_mem labels07_cover
theorem adjacency07 : ∀ x y : (Vertex07) ⊕ (Fin 3),
    graph08.Adj (labels07 x) (labels07 y) ↔ (tripleSubdivision graph07 a07 b07).Adj x y := by decide
theorem mappedGraph07 : (tripleSubdivision graph07 a07 b07).map labels07 = graph08 :=
  map_eq_of_forward (tripleSubdivision graph07 a07 b07) graph08 labels07 adjacency07
def chain08 : MoveChain IndependenceComplexTorsionSeed.G0 graph08 8 := by
  simpa only [mappedGraph07] using (MoveChain.triple chain07 a07 b07 edge07 labels07)

/- Certificate operation 8 (0-based): triple_subdivision. -/
def a08 : Vertex08 := ⟨34, by decide⟩
def b08 : Vertex08 := ⟨6, by decide⟩
theorem edge08 : graph08.Adj a08 b08 := by decide
def oldLabel08 : (Vertex08) → ℕ := fun x => x.val
def newLabel08 : Fin 3 → ℕ := ![35, 36, 37]
theorem newLabel08_injective : Function.Injective newLabel08 := by decide
theorem fresh08 : ∀ o : Vertex08, ∀ a : Fin 3, oldLabel08 o ≠ newLabel08 a := by decide
theorem labels08_mem : ∀ a : (Vertex08) ⊕ (Fin 3),
    Sum.elim oldLabel08 newLabel08 a ∈ vertices09 := by decide
theorem labels08_cover : ∀ t : Vertex09, ∃ a : (Vertex08) ⊕ (Fin 3),
    Sum.elim oldLabel08 newLabel08 a = t.val := by decide
def labels08 : ((Vertex08) ⊕ (Fin 3)) ≃ Vertex09 :=
  sumLabels vertices09 oldLabel08 newLabel08 (Subtype.val_injective)
    newLabel08_injective fresh08 labels08_mem labels08_cover
theorem adjacency08 : ∀ x y : (Vertex08) ⊕ (Fin 3),
    graph09.Adj (labels08 x) (labels08 y) ↔ (tripleSubdivision graph08 a08 b08).Adj x y := by decide
theorem mappedGraph08 : (tripleSubdivision graph08 a08 b08).map labels08 = graph09 :=
  map_eq_of_forward (tripleSubdivision graph08 a08 b08) graph09 labels08 adjacency08
def chain09 : MoveChain IndependenceComplexTorsionSeed.G0 graph09 9 := by
  simpa only [mappedGraph08] using (MoveChain.triple chain08 a08 b08 edge08 labels08)

/- Certificate operation 9 (0-based): triple_subdivision. -/
def a09 : Vertex09 := ⟨7, by decide⟩
def b09 : Vertex09 := ⟨8, by decide⟩
theorem edge09 : graph09.Adj a09 b09 := by decide
def oldLabel09 : (Vertex09) → ℕ := fun x => x.val
def newLabel09 : Fin 3 → ℕ := ![38, 39, 40]
theorem newLabel09_injective : Function.Injective newLabel09 := by decide
theorem fresh09 : ∀ o : Vertex09, ∀ a : Fin 3, oldLabel09 o ≠ newLabel09 a := by decide
theorem labels09_mem : ∀ a : (Vertex09) ⊕ (Fin 3),
    Sum.elim oldLabel09 newLabel09 a ∈ vertices10 := by decide
theorem labels09_cover : ∀ t : Vertex10, ∃ a : (Vertex09) ⊕ (Fin 3),
    Sum.elim oldLabel09 newLabel09 a = t.val := by decide
def labels09 : ((Vertex09) ⊕ (Fin 3)) ≃ Vertex10 :=
  sumLabels vertices10 oldLabel09 newLabel09 (Subtype.val_injective)
    newLabel09_injective fresh09 labels09_mem labels09_cover
theorem adjacency09 : ∀ x y : (Vertex09) ⊕ (Fin 3),
    graph10.Adj (labels09 x) (labels09 y) ↔ (tripleSubdivision graph09 a09 b09).Adj x y := by decide
theorem mappedGraph09 : (tripleSubdivision graph09 a09 b09).map labels09 = graph10 :=
  map_eq_of_forward (tripleSubdivision graph09 a09 b09) graph10 labels09 adjacency09
def chain10 : MoveChain IndependenceComplexTorsionSeed.G0 graph10 10 := by
  simpa only [mappedGraph09] using (MoveChain.triple chain09 a09 b09 edge09 labels09)

end D5.S3.Geometry.KingFiniteReplay
