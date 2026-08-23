/- GID: D5/S0/Diagonal/Lawvere/TheoryIsConsequenceFixedPoint
   generality: G
   mirror-B: D5/B/S0/Diagonal/Lawvere/TheoryIsConsequenceFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deductively closed sets are exactly fixed points of a consequence closure operator; their closures are least fixed points above generators and fixed points form a complete lattice under intersections, while the medium and strong forms are not covered. -/

import Mathlib.Order.Closure
import Mathlib.Order.FixedPoints

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'theory_iff_consequence_fixedPoint' D5 Golden/Frozen/accepted`
     found no repository declaration or accepted duplicate.
   * Repository searches for `ClosureOperator`, `deductively`, `consequence`, and
     theory/fixed-point combinations found no arbitrary consequence-operator theorem.
     Public hits `target_closure_equivalent_iff_target_sufficient` and
     `dynamic_closure_is_least` concern target-readout and intervention closures.
     The private hit `runWord_preserves_fiber` is only a local trajectory helper.
   * Pinned Mathlib's `ClosureOperator.isClosed_iff`, `isClosed_closure`,
     `closure_min`, `sInf_isClosed`, and `ClosureOperator.gi` give the required
     fixed-point, least-closure, intersection, and complete-lattice machinery.
   * Local smart searches for "ClosureOperator fixed point" and "deductively closed"
     had no name match. Online Loogle was unavailable through registered NyxID
     services, so the pinned Mathlib sources were searched directly.
   * `QualitativeEscape.escaped_of_fixedPointFree` is the public Lawvere core; it is
     orthogonal to consequence closure and is not reproved here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Diagonal.Lawvere.TheoryIsConsequenceFixedPoint

universe u

/-- A Tarskian consequence operator acts as a closure operator on sets of formulas. -/
abbrev ConsequenceOperator (Formula : Type u) := ClosureOperator (Set Formula)

/-- A set is a theory when it contains every consequence generated from itself. -/
def IsTheory {Formula : Type u} (Cn : ConsequenceOperator Formula)
    (S : Set Formula) : Prop :=
  Cn S ⊆ S

/-- The type of closed sets of a consequence operator. -/
abbrev Theory {Formula : Type u} (Cn : ConsequenceOperator Formula) := Cn.Closeds

/-- Closed sets inherit a complete lattice from their Galois insertion into all sets. -/
instance theoryCompleteLattice {Formula : Type u} (Cn : ConsequenceOperator Formula) :
    CompleteLattice (Theory Cn) :=
  Cn.gi.liftCompleteLattice

/-- A set is deductively closed exactly when it is a fixed point of consequence closure. -/
theorem theory_iff_consequence_fixedPoint
    {Formula : Type u} (Cn : ConsequenceOperator Formula) (S : Set Formula) :
    IsTheory Cn S ↔ S ∈ Function.fixedPoints Cn := by
  exact Cn.isClosed_iff_closure_le.symm.trans Cn.isClosed_iff

/-- Applying consequence closure always produces a fixed point. -/
theorem consequenceClosure_is_fixedPoint
    {Formula : Type u} (Cn : ConsequenceOperator Formula) (S : Set Formula) :
    Cn S ∈ Function.fixedPoints Cn := by
  exact Cn.idempotent S

/-- `Cn S` is the least fixed point of `Cn` that contains the generators `S`. -/
theorem consequenceClosure_isLeast_fixedPoint_above
    {Formula : Type u} (Cn : ConsequenceOperator Formula) (S : Set Formula) :
    IsLeast {T : Set Formula | S ⊆ T ∧ T ∈ Function.fixedPoints Cn} (Cn S) := by
  constructor
  · exact ⟨Cn.le_closure S, Cn.idempotent S⟩
  · intro T hT
    exact Cn.closure_min hT.1 (Cn.isClosed_iff.2 hT.2)

/-- Arbitrary intersections of fixed points are fixed points. -/
theorem fixedPoints_closed_under_sInf
    {Formula : Type u} (Cn : ConsequenceOperator Formula)
    (families : Set (Set Formula))
    (hfamilies : ∀ T ∈ families, T ∈ Function.fixedPoints Cn) :
    (sInf families : Set Formula) ∈ Function.fixedPoints Cn := by
  exact Cn.isClosed_iff.1 <|
    Cn.sInf_isClosed fun T hT => Cn.isClosed_iff.2 (hfamilies T hT)

example : IsTheory (ClosureOperator.id (Set Bool)) {true} := by
  rw [theory_iff_consequence_fixedPoint]
  rfl

#print axioms theory_iff_consequence_fixedPoint

end D5.S0.Diagonal.Lawvere.TheoryIsConsequenceFixedPoint
