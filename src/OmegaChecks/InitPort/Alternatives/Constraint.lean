module
public import Init.Omega.Constraint

open Lean.Omega

namespace OmegaChecks.InitPort.Alternatives

public theorem Lean.Omega.Constraint.not_sat_of_isImpossible :
    type_of% @_root_.Lean.Omega.Constraint.not_sat_of_isImpossible := by
  intro ⟨lo, hi⟩ impossible t satisfied
  cases lo with
  | none => exact Bool.noConfusion impossible
  | some l =>
    cases hi with
    | none => exact Bool.noConfusion impossible
    | some u =>
      have bounds : decide (l ≤ t) = true ∧ decide (t ≤ u) = true :=
        of_decide_eq_true satisfied
      exact Int.not_le_of_gt (of_decide_eq_true impossible)
        (Int.le_trans (of_decide_eq_true bounds.1) (of_decide_eq_true bounds.2))

private theorem all_merge {α : Type} (f : α → α → α) (p : α → Bool)
    (closed : ∀ x y, p x = true → p y = true → p (f x y) = true) :
    ∀ x y : Option α, x.all p = true → y.all p = true → (Option.merge f x y).all p = true
  | none, none, _, _ => rfl
  | none, some _, _, h => h
  | some _, none, h, _ => h
  | some x, some y, hx, hy => closed x y hx hy

public theorem Lean.Omega.Constraint.combine_sat' :
    type_of% @_root_.Lean.Omega.Constraint.combine_sat' := by
  intro s t x y hs ht
  let v := Coeffs.dot x y
  have sBounds : s.lowerBound.sat v ∧ s.upperBound.sat v := of_decide_eq_true hs
  have tBounds : t.lowerBound.sat v ∧ t.upperBound.sat v := of_decide_eq_true ht
  apply decide_eq_true
  constructor
  · exact all_merge max (fun a : Int => decide (a ≤ v))
      (fun _ _ h₁ h₂ => decide_eq_true (Int.max_le.mpr ⟨of_decide_eq_true h₁, of_decide_eq_true h₂⟩))
      _ _ sBounds.1 tBounds.1
  · exact all_merge min (fun a : Int => decide (v ≤ a))
      (fun _ _ h₁ h₂ => decide_eq_true (Int.le_min.mpr ⟨of_decide_eq_true h₁, of_decide_eq_true h₂⟩))
      _ _ sBounds.2 tBounds.2

end OmegaChecks.InitPort.Alternatives
