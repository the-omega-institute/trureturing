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

private theorem all_zip {α : Type} (op : α → α → α) (p q r : α → Bool)
    (closed : ∀ a b, p a = true → q b = true → r (op a b) = true) :
    ∀ a b : Option α, a.all p = true → b.all q = true →
      (a.bind fun x => b.map (op x)).all r = true
  | none, _, _, _ => rfl
  | some _, none, _, _ => rfl
  | some x, some y, hx, hy => closed x y hx hy

public theorem Lean.Omega.Constraint.add_sat :
    type_of% @_root_.Lean.Omega.Constraint.add_sat := by
  intro c₁ c₂ x₁ x₂ h₁ h₂
  have a : c₁.lowerBound.sat x₁ ∧ c₁.upperBound.sat x₁ := of_decide_eq_true h₁
  have b : c₂.lowerBound.sat x₂ ∧ c₂.upperBound.sat x₂ := of_decide_eq_true h₂
  apply decide_eq_true
  constructor
  · exact all_zip (· + ·) (fun x => decide (x ≤ x₁)) (fun y => decide (y ≤ x₂))
      (fun z => decide (z ≤ x₁ + x₂))
      (fun _ _ hx hy => decide_eq_true (Int.add_le_add (of_decide_eq_true hx) (of_decide_eq_true hy)))
      _ _ a.1 b.1
  · exact all_zip (· + ·) (fun x => decide (x₁ ≤ x)) (fun y => decide (x₂ ≤ y))
      (fun z => decide (x₁ + x₂ ≤ z))
      (fun _ _ hx hy => decide_eq_true (Int.add_le_add (of_decide_eq_true hx) (of_decide_eq_true hy)))
      _ _ a.2 b.2

private theorem all_map {α : Type} (f : α → α) (p q : α → Bool)
    (preserves : ∀ a, p a = true → q (f a) = true) :
    ∀ a : Option α, a.all p = true → (a.map f).all q = true
  | none, _ => rfl
  | some a, h => preserves a h

public theorem Lean.Omega.Constraint.scale_sat :
    type_of% @_root_.Lean.Omega.Constraint.scale_sat := by
  intro t c k h
  have bounds : c.lowerBound.sat t ∧ c.upperBound.sat t := of_decide_eq_true h
  by_cases zero : k = 0
  · subst k
    rw [_root_.Lean.Omega.Constraint.scale, ite_eq_left rfl, Int.zero_mul]
    split
    · rename_i impossible
      exact False.elim (Lean.Omega.Constraint.not_sat_of_isImpossible impossible h)
    · exact decide_eq_true ⟨decide_eq_true (Int.le_refl 0), decide_eq_true (Int.le_refl 0)⟩
  · rw [_root_.Lean.Omega.Constraint.scale, ite_eq_right zero]
    by_cases pos : 0 < k
    · rw [ite_eq_left pos]
      apply decide_eq_true
      constructor
      · exact all_map (k * ·) (fun a => decide (a ≤ t)) (fun a => decide (a ≤ k * t))
          (fun _ ha => decide_eq_true (Int.mul_le_mul_of_nonneg_left (of_decide_eq_true ha) (Int.le_of_lt pos))) _ bounds.1
      · exact all_map (k * ·) (fun a => decide (t ≤ a)) (fun a => decide (k * t ≤ a))
          (fun _ ha => decide_eq_true (Int.mul_le_mul_of_nonneg_left (of_decide_eq_true ha) (Int.le_of_lt pos))) _ bounds.2
    · rw [ite_eq_right pos]
      have nonpos := Int.le_of_not_gt pos
      apply decide_eq_true
      constructor
      · exact all_map (k * ·) (fun a => decide (t ≤ a)) (fun a => decide (a ≤ k * t))
          (fun _ ha => decide_eq_true (Int.mul_le_mul_of_nonpos_left nonpos (of_decide_eq_true ha))) _ bounds.2
      · exact all_map (k * ·) (fun a => decide (a ≤ t)) (fun a => decide (k * t ≤ a))
          (fun _ ha => decide_eq_true (Int.mul_le_mul_of_nonpos_left nonpos (of_decide_eq_true ha))) _ bounds.1

end OmegaChecks.InitPort.Alternatives
