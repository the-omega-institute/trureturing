/- GID: D5/S3/Arith/Lattices/FourGridCollinearTriples
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/FourGridCollinearTriples
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [Mathlib.Data.Fintype.BigOperators, Mathlib.Data.Finset.Powerset,
     Mathlib.Tactic.LinearCombination, Mathlib.Tactic.Linarith, Mathlib.Tactic.Ring]
   utility: none
   digest: Coordinatewise endpoint codes count arithmetic and four-point line candidates. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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

/-- The integral midpoint of two four-grid coordinates. -/
def midpointCoordinate (a b : Fin 4) : Fin 4 :=
  ⟨(a.val + b.val) / 2, by omega⟩

/-- The coordinatewise integral midpoint. -/
def midpoint {d : Nat} (x z : GridPoint d) : GridPoint d :=
  fun i => midpointCoordinate (x i) (z i)

/-- An oriented nonconstant arithmetic progression in the grid. -/
abbrev OrientedArithmeticProgression (d : Nat) :=
  {t : GridPoint d × GridPoint d × GridPoint d //
    t.1 ≠ t.2.2 ∧ ∀ i,
      ((t.1 i : Nat) : Int) + ((t.2.2 i : Nat) : Int) =
        2 * ((t.2.1 i : Nat) : Int)}

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

private def apEndpointEquiv (d : Nat) :
    DistinctCoordinatePairs SameParity d ≃ OrientedArithmeticProgression d where
  toFun p := by
    refine ⟨(p.val.val.1, midpoint p.val.val.1 p.val.val.2, p.val.val.2), p.property, ?_⟩
    intro i
    have hparity := p.val.property i
    unfold SameParity at hparity
    simp only [midpoint, midpointCoordinate]
    omega
  invFun t := by
    refine ⟨⟨(t.val.1, t.val.2.2), ?_⟩, t.property.1⟩
    intro i
    unfold SameParity
    change (t.val.1 i).val % 2 = (t.val.2.2 i).val % 2
    have hap := t.property.2 i
    have hapNat : (t.val.1 i).val + (t.val.2.2 i).val = 2 * (t.val.2.1 i).val := by
      exact_mod_cast hap
    omega
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        apply Fin.ext
        have hap := t.property.2 i
        simp only [midpoint, midpointCoordinate]
        omega
      · rfl

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

/-- There are `8^d - 4^d` oriented nonconstant arithmetic progressions in
the four-point grid. Reversing the endpoints is the remaining factor of two
for unordered arithmetic-progression triples. -/
theorem oriented_arithmetic_progression_count (d : Nat) :
    Fintype.card (OrientedArithmeticProgression d) = 8 ^ d - 4 ^ d := by
  rw [Fintype.card_congr (apEndpointEquiv d).symm]
  exact (endpoint_pair_counts d).1

/-- Once one coordinate spans zero to three, the minor equations force every
coordinate onto the same four-point line. The two conclusions distinguish the
two possible non-arithmetic-progression interior points. -/
theorem extreme_line_coordinate_classification {d : Nat} (x y z : GridPoint d) (k : Fin d)
    (hx : x k = 0) (hz : z k = 3) (hcol : Collinear x y z) :
    (y k = 1 -> ∀ i,
      (x i = y i ∧ y i = z i) ∨
        (x i = 0 ∧ y i = 1 ∧ z i = 3) ∨
        (x i = 3 ∧ y i = 2 ∧ z i = 0)) ∧
    (y k = 2 -> ∀ i,
      (x i = y i ∧ y i = z i) ∨
        (x i = 0 ∧ y i = 2 ∧ z i = 3) ∨
        (x i = 3 ∧ y i = 1 ∧ z i = 0)) := by
  constructor
  · intro hy i
    have h := hcol i k
    rw [hx, hy, hz] at h
    omega
  · intro hy i
    have h := hcol i k
    rw [hx, hy, hz] at h
    omega

private noncomputable def collinearTripleFinset (d : Nat) : Finset (Finset (GridPoint d)) := by
  classical
  exact ((Finset.univ : Finset (GridPoint d)).powersetCard 3).filter IsCollinearTriple

private abbrev CollinearTriples (d : Nat) := ↥(collinearTripleFinset d)

private noncomputable def orientationMark {d : Nat} (x z : GridPoint d) : Bool :=
  decide ((Fintype.equivFin (GridPoint d)) x < (Fintype.equivFin (GridPoint d)) z)

private noncomputable def apMarkedTriple {d : Nat} (t : OrientedArithmeticProgression d) :
    CollinearTriples d × Bool := by
  classical
  let x := t.val.1
  let y := t.val.2.1
  let z := t.val.2.2
  have hxz : x ≠ z := t.property.1
  have hxy : x ≠ y := by
    intro h
    apply hxz
    funext i
    apply Fin.ext
    have hi := t.property.2 i
    change ((x i : Nat) : Int) + ((z i : Nat) : Int) =
      2 * ((y i : Nat) : Int) at hi
    rw [h] at hi ⊢
    omega
  have hyz : y ≠ z := by
    intro h
    apply hxz
    funext i
    apply Fin.ext
    have hi := t.property.2 i
    change ((x i : Nat) : Int) + ((z i : Nat) : Int) =
      2 * ((y i : Nat) : Int) at hi
    rw [h] at hi
    omega
  have hbase : Collinear x y z := by
    intro i j
    have hi := t.property.2 i
    have hj := t.property.2 j
    change ((x i : Nat) : Int) + ((z i : Nat) : Int) =
      2 * ((y i : Nat) : Int) at hi
    change ((x j : Nat) : Int) + ((z j : Nat) : Int) =
      2 * ((y j : Nat) : Int) at hj
    have hi' : ((z i : Nat) : Int) - ((x i : Nat) : Int) =
        2 * (((y i : Nat) : Int) - ((x i : Nat) : Int)) := by
      linarith
    have hj' : ((z j : Nat) : Int) - ((x j : Nat) : Int) =
        2 * (((y j : Nat) : Int) - ((x j : Nat) : Int)) := by
      linarith
    rw [hi', hj']
    ring
  refine (⟨{x, y, z}, ?_⟩, orientationMark x z)
  change {x, y, z} ∈
    ((Finset.univ : Finset (GridPoint d)).powersetCard 3).filter IsCollinearTriple
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  refine ⟨⟨by simp, by simp [hxy, hxz, hyz]⟩, ?_⟩
  refine ⟨by simp [hxy, hxz, hyz], ?_⟩
  intro a ha b hb c hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with (rfl | rfl | rfl) <;>
    rcases hb with (rfl | rfl | rfl) <;>
      rcases hc with (rfl | rfl | rfl)
  all_goals
    unfold Collinear
    intro i j
    first
    | exact hbase i j
    | exact hbase j i
    | exact (hbase i j).symm
    | exact (hbase j i).symm
    | linear_combination hbase i j
    | linear_combination -hbase i j
    | linear_combination hbase j i
    | linear_combination -hbase j i
    | ring

private def extremeInteriorCoordinate (towardSecond : Bool) (x z : Fin 4) : Fin 4 :=
  ⟨(if towardSecond then x.val + 2 * z.val else 2 * x.val + z.val) / 3, by
    split <;> omega⟩

private def extremeInterior {d : Nat} (towardSecond : Bool) (x z : GridPoint d) :
    GridPoint d :=
  fun i => extremeInteriorCoordinate towardSecond (x i) (z i)

private noncomputable def extremeMarkedTriple {d : Nat}
    (q : DistinctCoordinatePairs EqualOrExtreme d × Bool) : CollinearTriples d × Bool := by
  classical
  let x := q.1.val.val.1
  let z := q.1.val.val.2
  let y := extremeInterior q.2 x z
  have hxz : x ≠ z := q.1.property
  have hcoord : ∃ k, x k ≠ z k := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hxz (funext h)
  let k := Classical.choose hcoord
  have hk : x k ≠ z k := Classical.choose_spec hcoord
  have hkrel := q.1.val.property k
  change EqualOrExtreme (x k) (z k) at hkrel
  have hkextreme :
      (x k).val = 0 ∧ (z k).val = 3 ∨ (x k).val = 3 ∧ (z k).val = 0 := by
    rcases hkrel with hEq | hExtreme | hExtreme
    · exact False.elim (hk hEq)
    · exact Or.inl hExtreme
    · exact Or.inr hExtreme
  have hxy : x ≠ y := by
    intro h
    have hkval := congrArg (fun p : GridPoint d => (p k).val) h
    change (x k).val = (extremeInteriorCoordinate q.2 (x k) (z k)).val at hkval
    rcases hkextreme with ⟨hx, hz⟩ | ⟨hx, hz⟩ <;>
      cases hq : q.2 <;>
        simp [extremeInteriorCoordinate, hx, hz, hq] at hkval
  have hyz : y ≠ z := by
    intro h
    have hkval := congrArg (fun p : GridPoint d => (p k).val) h
    change (extremeInteriorCoordinate q.2 (x k) (z k)).val = (z k).val at hkval
    rcases hkextreme with ⟨hx, hz⟩ | ⟨hx, hz⟩ <;>
      cases hq : q.2 <;>
        simp [extremeInteriorCoordinate, hx, hz, hq] at hkval
  have haffine (i : Fin d) :
      if q.2 then
        3 * ((y i : Nat) : Int) =
          ((x i : Nat) : Int) + 2 * ((z i : Nat) : Int)
      else
        3 * ((y i : Nat) : Int) =
          2 * ((x i : Nat) : Int) + ((z i : Nat) : Int) := by
    have hi := q.1.val.property i
    change EqualOrExtreme (x i) (z i) at hi
    rcases hi with hEq | hExtreme | hExtreme
    · cases hq : q.2 <;>
        simp [y, extremeInterior, extremeInteriorCoordinate, hEq, hq] <;> omega
    · rcases hExtreme with ⟨hx, hz⟩
      cases hq : q.2 <;>
        simp [y, extremeInterior, extremeInteriorCoordinate, hx, hz, hq]
    · rcases hExtreme with ⟨hx, hz⟩
      cases hq : q.2 <;>
        simp [y, extremeInterior, extremeInteriorCoordinate, hx, hz, hq]
  have hbase : Collinear x y z := by
    intro i j
    have hi := haffine i
    have hj := haffine j
    cases hq : q.2
    · rw [hq] at hi hj
      simp only [Bool.false_eq_true, ↓reduceIte] at hi hj
      have hi' : ((z i : Nat) : Int) - ((x i : Nat) : Int) =
          3 * (((y i : Nat) : Int) - ((x i : Nat) : Int)) := by
        linarith
      have hj' : ((z j : Nat) : Int) - ((x j : Nat) : Int) =
          3 * (((y j : Nat) : Int) - ((x j : Nat) : Int)) := by
        linarith
      rw [hi', hj']
      ring
    · rw [hq] at hi hj
      simp only [↓reduceIte] at hi hj
      have hi' : 2 * (((z i : Nat) : Int) - ((x i : Nat) : Int)) =
          3 * (((y i : Nat) : Int) - ((x i : Nat) : Int)) := by
        linarith
      have hj' : 2 * (((z j : Nat) : Int) - ((x j : Nat) : Int)) =
          3 * (((y j : Nat) : Int) - ((x j : Nat) : Int)) := by
        linarith
      nlinarith only [hi', hj']
  refine (⟨{x, y, z}, ?_⟩, orientationMark x z)
  change {x, y, z} ∈
    ((Finset.univ : Finset (GridPoint d)).powersetCard 3).filter IsCollinearTriple
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  refine ⟨⟨by simp, by simp [hxy, hxz, hyz]⟩, ?_⟩
  refine ⟨by simp [hxy, hxz, hyz], ?_⟩
  intro a ha b hb c hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with (rfl | rfl | rfl) <;>
    rcases hb with (rfl | rfl | rfl) <;>
      rcases hc with (rfl | rfl | rfl)
  all_goals
    unfold Collinear
    intro i j
    first
    | exact hbase i j
    | exact hbase j i
    | exact (hbase i j).symm
    | exact (hbase j i).symm
    | linear_combination hbase i j
    | linear_combination -hbase i j
    | linear_combination hbase j i
    | linear_combination -hbase j i
    | ring

private abbrev GeometricCode (d : Nat) :=
  OrientedArithmeticProgression d ⊕ (DistinctCoordinatePairs EqualOrExtreme d × Bool)

private noncomputable def codeToMarkedTriple {d : Nat} :
    GeometricCode d → CollinearTriples d × Bool
  | Sum.inl t => apMarkedTriple t
  | Sum.inr q => extremeMarkedTriple q

private def reverseArithmeticProgression {d : Nat} (t : OrientedArithmeticProgression d) :
    OrientedArithmeticProgression d := by
  refine ⟨(t.val.2.2, t.val.2.1, t.val.1), ?_, ?_⟩
  · exact Ne.symm t.property.1
  · intro i
    have hi := t.property.2 i
    linarith

private def reverseExtremeCode {d : Nat}
    (q : DistinctCoordinatePairs EqualOrExtreme d × Bool) :
    DistinctCoordinatePairs EqualOrExtreme d × Bool := by
  refine (⟨⟨(q.1.val.val.2, q.1.val.val.1), ?_⟩, Ne.symm q.1.property⟩, !q.2)
  intro i
  rcases q.1.val.property i with hEq | hExtreme | hExtreme
  · exact Or.inl hEq.symm
  · exact Or.inr (Or.inr ⟨hExtreme.2, hExtreme.1⟩)
  · exact Or.inr (Or.inl ⟨hExtreme.2, hExtreme.1⟩)

private def reverseGeometricCode {d : Nat} : GeometricCode d → GeometricCode d
  | Sum.inl t => Sum.inl (reverseArithmeticProgression t)
  | Sum.inr q => Sum.inr (reverseExtremeCode q)

#print axioms endpoint_pair_counts
#print axioms oriented_arithmetic_progression_count
#print axioms extreme_line_coordinate_classification

end D5.S3.Arith.Lattices.FourGridCollinearTriples
