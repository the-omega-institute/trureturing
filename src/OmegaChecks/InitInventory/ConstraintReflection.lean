module
public import Lean
import all Init.Omega.Constraint
public section

open Lean.Omega
namespace OmegaChecks.InitBoundaries.ConstraintReflection

/-- Equality of the propositions obtained by testing a Boolean conjunction. -/
def AndReflection : Prop := ∀ a b : Bool, ((a && b) = true) = ((a = true) ∧ (b = true))

/-- At zero the independently chosen lower and upper bounds realize all four Boolean pairs. -/
theorem ofCombine (rule : type_of% @Constraint.combine_sat) : AndReflection := by
  intro a b
  let lo : Bool → Constraint := fun pass => ⟨if pass then none else some 1, none⟩
  let hi : Bool → Constraint := fun pass => ⟨none, if pass then none else some (-1)⟩
  have h := rule (lo a) (hi b) 0
  cases a <;> cases b <;> exact h

private theorem mergeAll {α : Type} (f : α → α → α) (test : α → Bool)
    (combine : ∀ x y, test (f x y) = true ↔ test x = true ∧ test y = true)
    (x y : Option α) :
    (Option.merge f x y).all test = true ↔ x.all test = true ∧ y.all test = true := by
  cases x <;> cases y
  · exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩
  · exact ⟨fun h => ⟨rfl, h⟩, And.right⟩
  · exact ⟨fun h => ⟨h, rfl⟩, And.left⟩
  · exact combine _ _

theorem combineOfReflection (reflect : AndReflection) : type_of% @Constraint.combine_sat := by
  intro c d t
  let lo := mergeAll max (fun a : Int => decide (a ≤ t)) (fun _ _ =>
    ⟨fun h => ⟨decide_eq_true (Int.max_le.mp (of_decide_eq_true h)).1,
                decide_eq_true (Int.max_le.mp (of_decide_eq_true h)).2⟩,
     fun h => decide_eq_true (Int.max_le.mpr ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩)⟩)
    c.lowerBound d.lowerBound
  let hi := mergeAll min (fun a : Int => decide (t ≤ a)) (fun _ _ =>
    ⟨fun h => ⟨decide_eq_true (Int.le_min.mp (of_decide_eq_true h)).1,
                decide_eq_true (Int.le_min.mp (of_decide_eq_true h)).2⟩,
     fun h => decide_eq_true (Int.le_min.mpr ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩)⟩)
    c.upperBound d.upperBound
  have eq : (c.combine d).sat t = (c.sat t && d.sat t) := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      have w : (c.combine d).lowerBound.sat t ∧ (c.combine d).upperBound.sat t := of_decide_eq_true h
      obtain ⟨lc, ld⟩ := lo.mp w.1
      obtain ⟨uc, ud⟩ := hi.mp w.2
      exact Bool.and_eq_true_iff.mpr ⟨@decide_eq_true _ _ ⟨lc, uc⟩, @decide_eq_true _ _ ⟨ld, ud⟩⟩
    · intro h
      obtain ⟨cGood, dGood⟩ := Bool.and_eq_true_iff.mp h
      have wc : c.lowerBound.sat t ∧ c.upperBound.sat t := of_decide_eq_true cGood
      have wd : d.lowerBound.sat t ∧ d.upperBound.sat t := of_decide_eq_true dGood
      exact @decide_eq_true _ _ ⟨lo.mpr ⟨wc.1, wd.1⟩, hi.mpr ⟨wc.2, wd.2⟩⟩
  exact (congrArg (fun bit : Bool => bit = true) eq).trans (reflect _ _)

theorem equivalence : (type_of% @Constraint.combine_sat) ↔ AndReflection :=
  ⟨ofCombine, combineOfReflection⟩

end OmegaChecks.InitBoundaries.ConstraintReflection
