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

private def orientationMark_reverse {d : Nat} {x z : GridPoint d} (h : x ≠ z) :
    orientationMark z x = !orientationMark x z := by
  have hne : (Fintype.equivFin (GridPoint d)) x ≠ (Fintype.equivFin (GridPoint d)) z :=
    (Fintype.equivFin (GridPoint d)).injective.ne h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · simp [orientationMark, hlt, not_lt_of_ge hlt.le]
  · simp [orientationMark, hgt, not_lt_of_ge hgt.le]

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

private noncomputable def codeToMarkedTriple_reverse {d : Nat} (c : GeometricCode d) :
    codeToMarkedTriple (reverseGeometricCode c) =
      ((codeToMarkedTriple c).1, !(codeToMarkedTriple c).2) := by
  classical
  rcases c with t | q
  · apply Prod.ext
    · apply Subtype.ext
      change {t.val.2.2, t.val.2.1, t.val.1} = {t.val.1, t.val.2.1, t.val.2.2}
      ext p
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · exact orientationMark_reverse t.property.1
  · have hinterior :
        extremeInterior (!q.2) q.1.val.val.2 q.1.val.val.1 =
          extremeInterior q.2 q.1.val.val.1 q.1.val.val.2 := by
      funext i
      apply Fin.ext
      have hi := q.1.val.property i
      rcases hi with hEq | ⟨hx, hz⟩ | ⟨hx, hz⟩
      · cases q.2 <;>
          simp [extremeInterior, extremeInteriorCoordinate, hEq] <;> omega
      · cases hq : q.2 <;>
          simp [extremeInterior, extremeInteriorCoordinate, hx, hz]
      · cases hq : q.2 <;>
          simp [extremeInterior, extremeInteriorCoordinate, hx, hz]
    apply Prod.ext
    · apply Subtype.ext
      change
        {q.1.val.val.2, extremeInterior (!q.2) q.1.val.val.2 q.1.val.val.1,
            q.1.val.val.1} =
          {q.1.val.val.1, extremeInterior q.2 q.1.val.val.1 q.1.val.val.2,
            q.1.val.val.2}
      rw [hinterior]
      ext p
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · exact orientationMark_reverse q.1.property

set_option maxHeartbeats 800000 in
private noncomputable def codeToTriple_surjective {d : Nat} (s : CollinearTriples d) :
    ∃ c : GeometricCode d, (codeToMarkedTriple c).1 = s := by
  classical
  have hsfilter := s.property
  change s.val ∈
    ((Finset.univ : Finset (GridPoint d)).powersetCard 3).filter IsCollinearTriple at hsfilter
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hsfilter
  rcases Finset.card_eq_three.mp hsfilter.2.1 with ⟨x, y, z, hxy, hxz, hyz, hsxyz⟩
  have hxmem : x ∈ s.val := by rw [hsxyz]; simp
  have hymem : y ∈ s.val := by rw [hsxyz]; simp
  have hzmem : z ∈ s.val := by rw [hsxyz]; simp
  have hcol (a b c : GridPoint d) (ha : a ∈ s.val) (hb : b ∈ s.val)
      (hc : c ∈ s.val) : Collinear a b c :=
    hsfilter.2.2 a ha b hb c hc
  have hxyz := hcol x y z hxmem hymem hzmem
  have hcoord : ∃ k, x k ≠ y k := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hxy (funext h)
  let k := Classical.choose hcoord
  have hkxy : x k ≠ y k := Classical.choose_spec hcoord
  have hkxz : x k ≠ z k := by
    intro hk
    apply hxz
    funext i
    apply Fin.ext
    have hi := hxyz i k
    rw [hk] at hi
    simp only [sub_self, mul_zero, zero_eq_mul] at hi
    rcases hi with hcoeff | hdiff
    · exfalso
      apply hkxy
      have hyzK : y k = z k := by
        apply Fin.ext
        exact_mod_cast sub_eq_zero.mp hcoeff
      exact hk.trans hyzK.symm
    · have hzxI : (z i).val = (x i).val := by
        exact_mod_cast sub_eq_zero.mp hdiff
      exact hzxI.symm
  have hkyz : y k ≠ z k := by
    intro hk
    apply hyz
    funext i
    apply Fin.ext
    have hi := hxyz i k
    rw [hk] at hi
    have hcoeff : ((z k : Nat) : Int) - ((x k : Nat) : Int) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast (show (z k).val ≠ (x k).val from fun h => hkxz (Fin.ext h.symm))
    have hdiff :
        (((z k : Nat) : Int) - ((x k : Nat) : Int)) *
            ((((y i : Nat) : Int) - ((x i : Nat) : Int)) -
              (((z i : Nat) : Int) - ((x i : Nat) : Int))) = 0 := by
      linear_combination hi
    rcases mul_eq_zero.mp hdiff with hzero | hzero
    · exact False.elim (hcoeff hzero)
    · have hyzI : ((y i : Nat) : Int) = ((z i : Nat) : Int) := by linarith
      exact_mod_cast hyzI
  let APAt (a b c : GridPoint d) : Prop :=
    ((((b k : Nat) : Int) - ((a k : Nat) : Int) = 1 ∧
        ((c k : Nat) : Int) - ((a k : Nat) : Int) = 2) ∨
      (((b k : Nat) : Int) - ((a k : Nat) : Int) = -1 ∧
        ((c k : Nat) : Int) - ((a k : Nat) : Int) = -2))
  let ExtremeAt (a b c : GridPoint d) : Prop :=
    (a k).val = 0 ∧ (c k).val = 3 ∧ ((b k).val = 1 ∨ (b k).val = 2)
  have hpivot :
      APAt x y z ∨ APAt x z y ∨ APAt y x z ∨
      ExtremeAt x y z ∨ ExtremeAt x z y ∨ ExtremeAt y x z ∨
      ExtremeAt y z x ∨ ExtremeAt z x y ∨ ExtremeAt z y x := by
    dsimp only [APAt, ExtremeAt]
    have hkxyv : (x k).val ≠ (y k).val := fun h => hkxy (Fin.ext h)
    have hkxzv : (x k).val ≠ (z k).val := fun h => hkxz (Fin.ext h)
    have hkyzv : (y k).val ≠ (z k).val := fun h => hkyz (Fin.ext h)
    have horder :
        ((x k).val < (y k).val ∧ (y k).val < (z k).val) ∨
        ((x k).val < (z k).val ∧ (z k).val < (y k).val) ∨
        ((y k).val < (x k).val ∧ (x k).val < (z k).val) ∨
        ((y k).val < (z k).val ∧ (z k).val < (x k).val) ∨
        ((z k).val < (x k).val ∧ (x k).val < (y k).val) ∨
        ((z k).val < (y k).val ∧ (y k).val < (x k).val) := by
      omega
    rcases horder with h | h | h | h | h | h
    · have hc : APAt x y z ∨ ExtremeAt x y z := by
        dsimp only [APAt, ExtremeAt]
        omega
      exact hc.elim Or.inl (fun he => Or.inr (Or.inr (Or.inr (Or.inl he))))
    · have hc : APAt x z y ∨ ExtremeAt x z y := by
        dsimp only [APAt, ExtremeAt]
        omega
      exact hc.elim (fun ha => Or.inr (Or.inl ha))
        (fun he => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))
    · have hc : APAt y x z ∨ ExtremeAt y x z := by
        dsimp only [APAt, ExtremeAt]
        omega
      exact hc.elim (fun ha => Or.inr (Or.inr (Or.inl ha)))
        (fun he => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))))
    · have hc : APAt x z y ∨ ExtremeAt y z x := by
        dsimp only [APAt, ExtremeAt]
        omega
      exact hc.elim (fun ha => Or.inr (Or.inl ha))
        (fun he => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))))
    · have hc : APAt y x z ∨ ExtremeAt z x y := by
        dsimp only [APAt, ExtremeAt]
        omega
      exact hc.elim (fun ha => Or.inr (Or.inr (Or.inl ha)))
        (fun he => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl he))))))))
    · have hc : APAt x y z ∨ ExtremeAt z y x := by
        dsimp only [APAt, ExtremeAt]
        omega
      exact hc.elim Or.inl
        (fun he => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr he))))))))
  have makeAP (a b c : GridPoint d) (ha : a ∈ s.val) (hb : b ∈ s.val)
      (hc : c ∈ s.val) (hac : a ≠ c) (hset : {a, b, c} = s.val)
      (hp : APAt a b c) :
      ∃ code : GeometricCode d, (codeToMarkedTriple code).1 = s := by
    have habc := hcol a b c ha hb hc
    have hap (i : Fin d) :
        ((a i : Nat) : Int) + ((c i : Nat) : Int) = 2 * ((b i : Nat) : Int) := by
      have hi := habc i k
      rcases hp with ⟨hbk, hck⟩ | ⟨hbk, hck⟩ <;>
        rw [hbk, hck] at hi <;> norm_num at hi ⊢ <;> linarith
    let t : OrientedArithmeticProgression d := ⟨(a, b, c), hac, hap⟩
    refine ⟨Sum.inl t, ?_⟩
    apply Subtype.ext
    change {a, b, c} = s.val
    exact hset
  have makeExtreme (a b c : GridPoint d) (ha : a ∈ s.val) (hb : b ∈ s.val)
      (hc : c ∈ s.val) (hac : a ≠ c) (hset : {a, b, c} = s.val)
      (hp : ExtremeAt a b c) :
      ∃ code : GeometricCode d, (codeToMarkedTriple code).1 = s := by
    have ha0 : a k = 0 := by apply Fin.ext; exact hp.1
    have hc3 : c k = 3 := by apply Fin.ext; exact hp.2.1
    have habc := hcol a b c ha hb hc
    rcases hp.2.2 with hb1 | hb2
    · have hb1' : b k = 1 := by apply Fin.ext; exact hb1
      have hpattern :=
        (extreme_line_coordinate_classification a b c k ha0 hc3 habc).1 hb1'
      have hrel (i : Fin d) : EqualOrExtreme (a i) (c i) := by
        rcases hpattern i with hconstant | hforward | hreverse
        · exact Or.inl (hconstant.1.trans hconstant.2)
        · exact Or.inr (Or.inl ⟨by simpa using congrArg Fin.val hforward.1,
            by simpa using congrArg Fin.val hforward.2.2⟩)
        · exact Or.inr (Or.inr ⟨by simpa using congrArg Fin.val hreverse.1,
            by simpa using congrArg Fin.val hreverse.2.2⟩)
      have hinterior : b = extremeInterior false a c := by
        funext i
        apply Fin.ext
        rcases hpattern i with hconstant | hforward | hreverse
        · simp [extremeInterior, extremeInteriorCoordinate, ← hconstant.1,
            ← hconstant.2] <;> omega
        · simp [extremeInterior, extremeInteriorCoordinate, hforward]
        · simp [extremeInterior, extremeInteriorCoordinate, hreverse]
      let p : DistinctCoordinatePairs EqualOrExtreme d := ⟨⟨(a, c), hrel⟩, hac⟩
      refine ⟨Sum.inr (p, false), ?_⟩
      apply Subtype.ext
      change {a, extremeInterior false a c, c} = s.val
      rw [← hinterior]
      exact hset
    · have hb2' : b k = 2 := by apply Fin.ext; exact hb2
      have hpattern :=
        (extreme_line_coordinate_classification a b c k ha0 hc3 habc).2 hb2'
      have hrel (i : Fin d) : EqualOrExtreme (a i) (c i) := by
        rcases hpattern i with hconstant | hforward | hreverse
        · exact Or.inl (hconstant.1.trans hconstant.2)
        · exact Or.inr (Or.inl ⟨by simpa using congrArg Fin.val hforward.1,
            by simpa using congrArg Fin.val hforward.2.2⟩)
        · exact Or.inr (Or.inr ⟨by simpa using congrArg Fin.val hreverse.1,
            by simpa using congrArg Fin.val hreverse.2.2⟩)
      have hinterior : b = extremeInterior true a c := by
        funext i
        apply Fin.ext
        rcases hpattern i with hconstant | hforward | hreverse
        · simp [extremeInterior, extremeInteriorCoordinate, ← hconstant.1,
            ← hconstant.2] <;> omega
        · simp [extremeInterior, extremeInteriorCoordinate, hforward]
        · simp [extremeInterior, extremeInteriorCoordinate, hreverse]
      let p : DistinctCoordinatePairs EqualOrExtreme d := ⟨⟨(a, c), hrel⟩, hac⟩
      refine ⟨Sum.inr (p, true), ?_⟩
      apply Subtype.ext
      change {a, extremeInterior true a c, c} = s.val
      rw [← hinterior]
      exact hset
  rcases hpivot with hp | hp | hp | hp | hp | hp | hp | hp | hp
  · exact makeAP x y z hxmem hymem hzmem hxz (by rw [hsxyz]) hp
  · exact makeAP x z y hxmem hzmem hymem hxy (by rw [hsxyz]; ext; simp; tauto) hp
  · exact makeAP y x z hymem hxmem hzmem hyz (by rw [hsxyz]; ext; simp; tauto) hp
  · exact makeExtreme x y z hxmem hymem hzmem hxz (by rw [hsxyz]) hp
  · exact makeExtreme x z y hxmem hzmem hymem hxy (by rw [hsxyz]; ext; simp; tauto) hp
  · exact makeExtreme y x z hymem hxmem hzmem hyz (by rw [hsxyz]; ext; simp; tauto) hp
  · exact makeExtreme y z x hymem hzmem hxmem hxy.symm (by rw [hsxyz]; ext; simp; tauto) hp
  · exact makeExtreme z x y hzmem hxmem hymem hyz.symm (by rw [hsxyz]; ext; simp; tauto) hp
  · exact makeExtreme z y x hzmem hymem hxmem hxz.symm (by rw [hsxyz]; ext; simp; tauto) hp

private noncomputable def apMarkedTriple_injective {d : Nat} :
    Function.Injective (apMarkedTriple : OrientedArithmeticProgression d →
      CollinearTriples d × Bool) := by
  classical
  intro t u htu
  let x := t.val.1
  let y := t.val.2.1
  let z := t.val.2.2
  let X := u.val.1
  let Y := u.val.2.1
  let Z := u.val.2.2
  have hxz : x ≠ z := t.property.1
  have hXZ : X ≠ Z := u.property.1
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
  have hXY : X ≠ Y := by
    intro h
    apply hXZ
    funext i
    apply Fin.ext
    have hi := u.property.2 i
    change ((X i : Nat) : Int) + ((Z i : Nat) : Int) =
      2 * ((Y i : Nat) : Int) at hi
    rw [h] at hi ⊢
    omega
  have hYZ : Y ≠ Z := by
    intro h
    apply hXZ
    funext i
    apply Fin.ext
    have hi := u.property.2 i
    change ((X i : Nat) : Int) + ((Z i : Nat) : Int) =
      2 * ((Y i : Nat) : Int) at hi
    rw [h] at hi
    omega
  have hfin := congrArg (fun p => p.1.val) htu
  have hmark := congrArg Prod.snd htu
  change {x, y, z} = {X, Y, Z} at hfin
  change orientationMark x z = orientationMark X Z at hmark
  have hcenter : y = Y := by
    funext i
    apply Fin.ext
    have hsum := congrArg
      (fun s : Finset (GridPoint d) => ∑ p ∈ s, ((p i : Nat) : Int)) hfin
    simp [hxy, hxz, hyz, hXY, hXZ, hYZ] at hsum
    have ht := t.property.2 i
    have hu := u.property.2 i
    change ((x i : Nat) : Int) + ((z i : Nat) : Int) =
      2 * ((y i : Nat) : Int) at ht
    change ((X i : Nat) : Int) + ((Z i : Nat) : Int) =
      2 * ((Y i : Nat) : Int) at hu
    have hval : ((y i : Nat) : Int) = ((Y i : Nat) : Int) := by linarith
    exact_mod_cast hval
  have hendpoints : (x = X ∧ z = Z) ∨ (x = Z ∧ z = X) := by
    have hxmem : x ∈ ({X, Y, Z} : Finset (GridPoint d)) := by rw [← hfin]; simp
    have hzmem : z ∈ ({X, Y, Z} : Finset (GridPoint d)) := by rw [← hfin]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem hzmem
    grind
  rcases hendpoints with ⟨hx, hz⟩ | ⟨hx, hz⟩
  · apply Subtype.ext
    exact Prod.ext hx (Prod.ext hcenter hz)
  · rw [← hz, ← hx] at hmark
    have hreverse := orientationMark_reverse hxz
    rw [hreverse] at hmark
    cases hq : orientationMark x z <;> simp [hq] at hmark

private noncomputable def extremeMarkedTriple_injective {d : Nat} :
    Function.Injective (extremeMarkedTriple :
      DistinctCoordinatePairs EqualOrExtreme d × Bool → CollinearTriples d × Bool) := by
  classical
  intro q r hqr
  let x := q.1.val.val.1
  let z := q.1.val.val.2
  let y := extremeInterior q.2 x z
  let X := r.1.val.val.1
  let Z := r.1.val.val.2
  let Y := extremeInterior r.2 X Z
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
  have hkxy : x k ≠ y k := by
    intro h
    have hv := congrArg Fin.val h
    change (x k).val = (extremeInteriorCoordinate q.2 (x k) (z k)).val at hv
    rcases hkextreme with ⟨hx, hz⟩ | ⟨hx, hz⟩ <;>
      cases hq : q.2 <;> simp [extremeInteriorCoordinate, hx, hz, hq] at hv
  have hkyz : y k ≠ z k := by
    intro h
    have hv := congrArg Fin.val h
    change (extremeInteriorCoordinate q.2 (x k) (z k)).val = (z k).val at hv
    rcases hkextreme with ⟨hx, hz⟩ | ⟨hx, hz⟩ <;>
      cases hq : q.2 <;> simp [extremeInteriorCoordinate, hx, hz, hq] at hv
  have hxy : x ≠ y := fun h => hkxy (congrFun h k)
  have hyz : y ≠ z := fun h => hkyz (congrFun h k)
  have hnotXY : ¬EqualOrExtreme (x k) (y k) := by
    intro hrel
    rcases hrel with hEq | hExtreme | hExtreme
    · exact hkxy hEq
    · rcases hExtreme with ⟨hx0, hy3⟩
      have hv : (y k).val =
          (extremeInteriorCoordinate q.2 (x k) (z k)).val := rfl
      rcases hkextreme with ⟨hx, hz⟩ | ⟨hx, hz⟩ <;>
        cases hq : q.2 <;>
          simp [extremeInteriorCoordinate, hx, hz, hq] at hv <;> omega
    · rcases hExtreme with ⟨hx3, hy0⟩
      have hv : (y k).val =
          (extremeInteriorCoordinate q.2 (x k) (z k)).val := rfl
      rcases hkextreme with ⟨hx, hz⟩ | ⟨hx, hz⟩ <;>
        cases hq : q.2 <;>
          simp [extremeInteriorCoordinate, hx, hz, hq] at hv <;> omega
  have hnotYX : ¬EqualOrExtreme (y k) (x k) := by
    intro hrel
    apply hnotXY
    rcases hrel with hEq | hExtreme | hExtreme
    · exact Or.inl hEq.symm
    · exact Or.inr (Or.inr ⟨hExtreme.2, hExtreme.1⟩)
    · exact Or.inr (Or.inl ⟨hExtreme.2, hExtreme.1⟩)
  have hnotYZ : ¬EqualOrExtreme (y k) (z k) := by
    intro hrel
    rcases hrel with hEq | hExtreme | hExtreme
    · exact hkyz hEq
    · rcases hExtreme with ⟨hy0, hz3⟩
      have hv : (y k).val =
          (extremeInteriorCoordinate q.2 (x k) (z k)).val := rfl
      rcases hkextreme with ⟨hx, hz⟩ | ⟨hx, hz⟩ <;>
        cases hq : q.2 <;>
          simp [extremeInteriorCoordinate, hx, hz, hq] at hv <;> omega
    · rcases hExtreme with ⟨hy3, hz0⟩
      have hv : (y k).val =
          (extremeInteriorCoordinate q.2 (x k) (z k)).val := rfl
      rcases hkextreme with ⟨hx, hz⟩ | ⟨hx, hz⟩ <;>
        cases hq : q.2 <;>
          simp [extremeInteriorCoordinate, hx, hz, hq] at hv <;> omega
  have hnotZY : ¬EqualOrExtreme (z k) (y k) := by
    intro hrel
    apply hnotYZ
    rcases hrel with hEq | hExtreme | hExtreme
    · exact Or.inl hEq.symm
    · exact Or.inr (Or.inr ⟨hExtreme.2, hExtreme.1⟩)
    · exact Or.inr (Or.inl ⟨hExtreme.2, hExtreme.1⟩)
  have hfin := congrArg (fun p => p.1.val) hqr
  have hmark := congrArg Prod.snd hqr
  change {x, y, z} = {X, Y, Z} at hfin
  change orientationMark x z = orientationMark X Z at hmark
  have hXmem : X ∈ ({x, y, z} : Finset (GridPoint d)) := by rw [hfin]; simp
  have hZmem : Z ∈ ({x, y, z} : Finset (GridPoint d)) := by rw [hfin]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hXmem hZmem
  have hrrel := r.1.val.property k
  change EqualOrExtreme (X k) (Z k) at hrrel
  have hXZ : X ≠ Z := r.1.property
  have hendpoints : (X = x ∧ Z = z) ∨ (X = z ∧ Z = x) := by
    rcases hXmem with hX | hX | hX <;> rcases hZmem with hZ | hZ | hZ
    · exact False.elim (hXZ (hX.trans hZ.symm))
    · rw [hX, hZ] at hrrel
      exact False.elim (hnotXY hrrel)
    · exact Or.inl ⟨hX, hZ⟩
    · rw [hX, hZ] at hrrel
      exact False.elim (hnotYX hrrel)
    · exact False.elim (hXZ (hX.trans hZ.symm))
    · rw [hX, hZ] at hrrel
      exact False.elim (hnotYZ hrrel)
    · exact Or.inr ⟨hX, hZ⟩
    · rw [hX, hZ] at hrrel
      exact False.elim (hnotZY hrrel)
    · exact False.elim (hXZ (hX.trans hZ.symm))
  rcases hendpoints with ⟨hX, hZ⟩ | ⟨hX, hZ⟩
  · have hcenter : y = Y := by
      have hymem : y ∈ ({X, Y, Z} : Finset (GridPoint d)) := by rw [← hfin]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hymem
      grind
    have hchoice : q.2 = r.2 := by
      by_contra hchoice
      have hv := congrArg (fun p : GridPoint d => (p k).val) hcenter
      change (extremeInteriorCoordinate q.2 (x k) (z k)).val =
        (extremeInteriorCoordinate r.2 (X k) (Z k)).val at hv
      rw [hX, hZ] at hv
      rcases hkextreme with ⟨hx, hz⟩ | ⟨hx, hz⟩ <;>
        cases hq : q.2 <;> cases hr : r.2 <;>
          simp [extremeInteriorCoordinate, hx, hz, hq, hr] at hv hchoice
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext hX.symm hZ.symm
    · exact hchoice
  · rw [hX, hZ] at hmark
    have hreverse := orientationMark_reverse hxz
    rw [hreverse] at hmark
    cases hq : orientationMark x z <;> simp [hq] at hmark

private noncomputable def apMarkedTriple_ne_extremeMarkedTriple {d : Nat}
    (t : OrientedArithmeticProgression d)
    (q : DistinctCoordinatePairs EqualOrExtreme d × Bool) :
    apMarkedTriple t ≠ extremeMarkedTriple q := by
  classical
  intro heq
  let a := t.val.1
  let b := t.val.2.1
  let c := t.val.2.2
  let x := q.1.val.val.1
  let z := q.1.val.val.2
  let y := extremeInterior q.2 x z
  have hac : a ≠ c := t.property.1
  have hab : a ≠ b := by
    intro h
    apply hac
    funext i
    apply Fin.ext
    have hi := t.property.2 i
    change ((a i : Nat) : Int) + ((c i : Nat) : Int) =
      2 * ((b i : Nat) : Int) at hi
    rw [h] at hi ⊢
    omega
  have hbc : b ≠ c := by
    intro h
    apply hac
    funext i
    apply Fin.ext
    have hi := t.property.2 i
    change ((a i : Nat) : Int) + ((c i : Nat) : Int) =
      2 * ((b i : Nat) : Int) at hi
    rw [h] at hi
    omega
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
  have hkxy : x k ≠ y k := by
    intro h
    have hv := congrArg Fin.val h
    change (x k).val = (extremeInteriorCoordinate q.2 (x k) (z k)).val at hv
    rcases hkextreme with ⟨hx, hz⟩ | ⟨hx, hz⟩ <;>
      cases hq : q.2 <;> simp [extremeInteriorCoordinate, hx, hz, hq] at hv
  have hkyz : y k ≠ z k := by
    intro h
    have hv := congrArg Fin.val h
    change (extremeInteriorCoordinate q.2 (x k) (z k)).val = (z k).val at hv
    rcases hkextreme with ⟨hx, hz⟩ | ⟨hx, hz⟩ <;>
      cases hq : q.2 <;> simp [extremeInteriorCoordinate, hx, hz, hq] at hv
  have hxy : x ≠ y := fun h => hkxy (congrFun h k)
  have hyz : y ≠ z := fun h => hkyz (congrFun h k)
  have hfin := congrArg (fun p => p.1.val) heq
  change {a, b, c} = {x, y, z} at hfin
  have hbmem : b ∈ ({x, y, z} : Finset (GridPoint d)) := by rw [← hfin]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbmem
  have hsum := congrArg
    (fun s : Finset (GridPoint d) => ∑ p ∈ s, ((p k : Nat) : Int)) hfin
  simp [hab, hac, hbc, hxy, hxz, hyz] at hsum
  have hap := t.property.2 k
  change ((a k : Nat) : Int) + ((c k : Nat) : Int) =
    2 * ((b k : Nat) : Int) at hap
  rcases hbmem with hb | hb | hb
  all_goals
    have hbval := congrArg (fun p : GridPoint d => (p k).val) hb
    rcases hkextreme with ⟨hx, hz⟩ | ⟨hx, hz⟩ <;>
      cases hq : q.2 <;>
        simp [y, extremeInterior, extremeInteriorCoordinate, hx, hz, hq] at hsum hbval <;>
          omega

private noncomputable def geometricCodeEquiv (d : Nat) :
    GeometricCode d ≃ CollinearTriples d × Bool :=
  Equiv.ofBijective codeToMarkedTriple (by
    constructor
    · intro c₁ c₂ h
      rcases c₁ with t | q <;> rcases c₂ with u | r
      · exact congrArg Sum.inl (apMarkedTriple_injective h)
      · exact False.elim (apMarkedTriple_ne_extremeMarkedTriple t r h)
      · exact False.elim (apMarkedTriple_ne_extremeMarkedTriple u q h.symm)
      · exact congrArg Sum.inr (extremeMarkedTriple_injective h)
    · rintro ⟨s, mark⟩
      obtain ⟨c, hc⟩ := codeToTriple_surjective s
      by_cases hm : (codeToMarkedTriple c).2 = mark
      · refine ⟨c, ?_⟩
        exact Prod.ext hc hm
      · refine ⟨reverseGeometricCode c, ?_⟩
        rw [codeToMarkedTriple_reverse]
        apply Prod.ext
        · exact hc
        · cases hcode : (codeToMarkedTriple c).2 <;> cases hmark : mark <;>
            simp [hcode, hmark] at hm ⊢)

/-- The number of unordered collinear triples in the four-point `d`-grid
satisfies the conjectured Mathar formula without introducing division. -/
theorem mathar_collinear_triples (d : ℕ) :
    2 * matharCount d = 8 ^ d + 2 * 6 ^ d - 3 * 4 ^ d := by
  classical
  have hcard := Fintype.card_congr (geometricCodeEquiv d)
  simp only [GeometricCode, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_bool] at hcard
  have htriples : Fintype.card (CollinearTriples d) = matharCount d := by
    rw [Fintype.card_coe]
    rfl
  rw [oriented_arithmetic_progression_count, (endpoint_pair_counts d).2, htriples] at hcard
  have hfourEight : 4 ^ d ≤ 8 ^ d := Nat.pow_le_pow_left (by omega) d
  have hfourSix : 4 ^ d ≤ 6 ^ d := Nat.pow_le_pow_left (by omega) d
  omega

example (d : ℕ) :
    matharCount d = (8 ^ d + 2 * 6 ^ d - 3 * 4 ^ d) / 2 := by
  have h := mathar_collinear_triples d
  omega

#print axioms endpoint_pair_counts
#print axioms oriented_arithmetic_progression_count
#print axioms extreme_line_coordinate_classification
#print axioms mathar_collinear_triples

end D5.S3.Arith.Lattices.FourGridCollinearTriples
