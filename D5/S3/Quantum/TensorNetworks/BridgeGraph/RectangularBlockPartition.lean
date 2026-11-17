/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/RectangularBlockPartition
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/RectangularBlockPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal-cardinality rectangle partitions give unitary paired factors and exact realignment rank. -/

import D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section
open Matrix
open scoped BigOperators

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.RectangularBlockPartition

universe u v w z
variable {X : Type u} {Y : Type v} {T : Type w}
  [Fintype X] [Fintype Y] [Fintype T] [DecidableEq X] [DecidableEq Y]
  (I : T → Finset X) (J : T → Finset Y)
  (φ : ∀ t, {y // y ∈ J t} ≃ {x // x ∈ I t})

def block (t : T) : Matrix X Y ℂ := by
  classical
  exact fun i j => if ∃ y : {y // y ∈ J t}, y.val = j ∧ (φ t y).val = i then 1 else 0

def operator : Matrix (X × Y) (Y × X) ℂ :=
  ∑ t, kronecker (block I J φ t) (block I J φ t)ᴴ

/-- The local carriers of the two factors determine this order of realignment. -/
def realign (U : Matrix (X × Y) (Y × X) ℂ) : Matrix (X × Y) (Y × X) ℂ :=
  fun p q => U (p.1, q.1) (p.2, q.2)

/-- Empty blocks are omitted from the achieved factor count. -/
def Active := {t // (J t).Nonempty}

private def flatten
    (h : ∀ x y, ∃! t, x ∈ I t ∧ y ∈ J t) :
    (Σ t, {x // x ∈ I t} × {y // y ∈ J t}) ≃ X × Y :=
  Equiv.ofBijective (fun a => (a.2.1.val, a.2.2.val)) (by
    constructor
    · rintro ⟨t, x, y⟩ ⟨s, x', y'⟩ he
      have hx : x.val = x'.val := congrArg Prod.fst he
      have hy : y.val = y'.val := congrArg Prod.snd he
      have ht : t = s := (h x.val y.val).unique ⟨x.property, y.property⟩
        ⟨hx ▸ x'.property, hy ▸ y'.property⟩
      subst s
      have hxx : x = x' := Subtype.ext hx
      have hyy : y = y' := Subtype.ext hy
      subst x'; subst y'
      rfl
    · rintro ⟨x, y⟩
      obtain ⟨t, ht, _⟩ := h x y
      exact ⟨⟨t, ⟨x, ht.1⟩, ⟨y, ht.2⟩⟩, rfl⟩)

/-- The input (j,l) is routed within its unique rectangle to (φ(j),φ⁻¹(l)). -/
def route (h : ∀ x y, ∃! t, x ∈ I t ∧ y ∈ J t) : (Y × X) ≃ (X × Y) :=
  ((Equiv.prodComm Y X).trans (flatten I J h).symm).trans
    ((Equiv.sigmaCongrRight (fun t =>
      (Equiv.prodComm {x // x ∈ I t} {y // y ∈ J t}).trans
        ((φ t).prodCongr (φ t).symm))).trans (flatten I J h))

end D5.S3.Quantum.TensorNetworks.BridgeGraph.RectangularBlockPartition
