/- GID: D5/S3/Arith/Lattices/FourGridCollinearTriples
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/FourGridCollinearTriples
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [Mathlib.Data.Fintype.BigOperators, Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Coordinatewise endpoint codes count arithmetic and four-point line candidates. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators

namespace D5.S3.Arith.Lattices.FourGridCollinearTriples

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A point of the `d`-dimensional grid with four points on every axis. -/
abbrev GridPoint (d : Nat) := Fin d -> Fin 4

/-- Collinearity expressed by the vanishing of all integral two-by-two minors. -/
def Collinear {d : Nat} (x y z : GridPoint d) : Prop :=
  forall i j,
    (((y i : Nat) : Int) - ((x i : Nat) : Int)) *
        (((z j : Nat) : Int) - ((x j : Nat) : Int)) =
      (((y j : Nat) : Int) - ((x j : Nat) : Int)) *
        (((z i : Nat) : Int) - ((x i : Nat) : Int))

/-- An unordered three-point subset whose points satisfy the minor equations. -/
def IsCollinearTriple {d : Nat} (s : Finset (GridPoint d)) : Prop :=
  s.card = 3 ∧
    ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, Collinear x y z

/-- The number of unordered collinear triples in the four-point grid. -/
noncomputable def matharCount (d : Nat) : Nat := by
  classical
  exact (((Finset.univ : Finset (GridPoint d)).powersetCard 3).filter IsCollinearTriple).card

/-- Two axis coordinates have the same parity. -/
def SameParity (a b : Fin 4) : Prop := a.val % 2 = b.val % 2

instance : DecidableRel SameParity := fun a b => by
  unfold SameParity
  infer_instance

/-- Two axis coordinates are equal or are the two extremes zero and three. -/
def EqualOrExtreme (a b : Fin 4) : Prop :=
  a = b ∨ (a.val = 0 ∧ b.val = 3) ∨ (a.val = 3 ∧ b.val = 0)

instance : DecidableRel EqualOrExtreme := fun a b => by
  unfold EqualOrExtreme
  infer_instance

/-- Ordered endpoint pairs satisfying a coordinate relation in every coordinate. -/
abbrev CoordinatePairs (relation : Fin 4 -> Fin 4 -> Prop) (d : Nat) :=
  {p : GridPoint d × GridPoint d // ∀ i, relation (p.1 i) (p.2 i)}

/-- Coordinatewise permitted endpoint pairs with unequal endpoints. -/
abbrev DistinctCoordinatePairs (relation : Fin 4 -> Fin 4 -> Prop) (d : Nat) :=
  {p : CoordinatePairs relation d // p.val.1 ≠ p.val.2}

private def coordinatePairsEquiv (relation : Fin 4 -> Fin 4 -> Prop) (d : Nat) :
    CoordinatePairs relation d ≃ (Fin d -> {q : Fin 4 × Fin 4 // relation q.1 q.2}) where
  toFun p i := ⟨(p.val.1 i, p.val.2 i), p.property i⟩
  invFun f := ⟨(fun i => (f i).val.1, fun i => (f i).val.2), fun i => (f i).property⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl rfl
  right_inv f := by
    funext i
    exact Subtype.ext (by rfl)

private def diagonalCoordinatePairsEquiv (relation : Fin 4 -> Fin 4 -> Prop)
    (reflexive : ∀ a, relation a a) (d : Nat) :
    {p : CoordinatePairs relation d // p.val.1 = p.val.2} ≃ GridPoint d where
  toFun p := p.val.val.1
  invFun x := ⟨⟨(x, x), fun i => reflexive (x i)⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl p.property
  right_inv _ := rfl

/-- The ordered endpoint codes consist of `8^d - 4^d` nonconstant parity
pairs and `6^d - 4^d` nonconstant extreme pairs. -/
theorem endpoint_pair_counts (d : Nat) :
    Fintype.card (DistinctCoordinatePairs SameParity d) = 8 ^ d - 4 ^ d ∧
      Fintype.card (DistinctCoordinatePairs EqualOrExtreme d) = 6 ^ d - 4 ^ d := by
  have count_of_relation (relation : Fin 4 -> Fin 4 -> Prop) [DecidableRel relation]
      (reflexive : ∀ a, relation a a) (coordinateCard : Nat)
      (hcoordinate : Fintype.card {q : Fin 4 × Fin 4 // relation q.1 q.2} = coordinateCard) :
      Fintype.card (DistinctCoordinatePairs relation d) = coordinateCard ^ d - 4 ^ d := by
    change Fintype.card {p : CoordinatePairs relation d // ¬(p.val.1 = p.val.2)} = _
    rw [Fintype.card_subtype_compl]
    congr 1
    · calc
        Fintype.card (CoordinatePairs relation d) =
            Fintype.card (Fin d -> {q : Fin 4 × Fin 4 // relation q.1 q.2}) :=
          Fintype.card_congr (coordinatePairsEquiv relation d)
        _ = Fintype.card {q : Fin 4 × Fin 4 // relation q.1 q.2} ^ d := by
          exact Fintype.card_pi_const _ d
        _ = coordinateCard ^ d := by rw [hcoordinate]
    · calc
        Fintype.card {p : CoordinatePairs relation d // p.val.1 = p.val.2} =
            Fintype.card (GridPoint d) :=
          Fintype.card_congr (diagonalCoordinatePairsEquiv relation reflexive d)
        _ = 4 ^ d := by exact Fintype.card_pi_const _ d
  constructor
  · apply count_of_relation SameParity (fun _ => rfl) 8
    decide
  · apply count_of_relation EqualOrExtreme (fun _ => Or.inl rfl) 6
    decide

#print axioms endpoint_pair_counts

end D5.S3.Arith.Lattices.FourGridCollinearTriples
