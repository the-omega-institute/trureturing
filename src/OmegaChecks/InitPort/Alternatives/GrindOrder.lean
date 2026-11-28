module
import all Init.Grind.Offset
import all Init.Grind.Norm
import all Init.Grind.Lemmas

/-! Constructive propagation of offset, Boolean, and logical constraints. -/

namespace OmegaChecks.InitPort.Alternatives

private theorem notOfEqFalse {p : Prop} (eq : p = False) : ¬p := fun hp => Eq.mp eq hp

public theorem Lean.Grind.Nat.of_le_eq_false : type_of% @_root_.Lean.Grind.Nat.of_le_eq_false :=
  fun _ _ eq => Nat.lt_of_not_ge (notOfEqFalse eq)

public theorem Lean.Grind.Nat.of_lo_eq_false_1 : type_of% @_root_.Lean.Grind.Nat.of_lo_eq_false_1 :=
  fun _ _ eq => Nat.le_of_not_gt (notOfEqFalse eq)

public theorem Lean.Grind.Nat.of_lo_eq_false : type_of% @_root_.Lean.Grind.Nat.of_lo_eq_false := by
  intro u v k eq
  have lt := Nat.lt_of_not_ge (notOfEqFalse eq)
  cases k with
  | zero => exact Nat.le_of_lt lt
  | succ k => exact Nat.le_of_lt_succ lt

public theorem Lean.Grind.Nat.of_ro_eq_false : type_of% @_root_.Lean.Grind.Nat.of_ro_eq_false :=
  fun _ _ _ eq => Nat.lt_of_not_ge (notOfEqFalse eq)

public theorem Lean.Grind.false_of_not_eq_self : type_of% @_root_.Lean.Grind.false_of_not_eq_self := by
  intro a eq
  have neg : ¬a := fun ha => (eq.mpr ha) ha
  exact neg (eq.mp neg)

public theorem Lean.Grind.decide_eq_true : type_of% @_root_.Lean.Grind.decide_eq_true :=
  fun eq => _root_.decide_eq_true (eq.mpr True.intro)

public theorem Lean.Grind.decide_eq_false : type_of% @_root_.Lean.Grind.decide_eq_false :=
  fun eq => _root_.decide_eq_false (notOfEqFalse eq)

public theorem Lean.Grind.bne_eq_decide_not_eq : type_of% @_root_.Lean.Grind.bne_eq_decide_not_eq := by
  intro α _ _ _ a b
  cases h : (a == b) with
  | false =>
    have neq : a ≠ b := beq_eq_false_iff_ne.mp h
    change (!(a == b)) = decide (a ≠ b)
    rw [h, _root_.decide_eq_true neq]
    rfl
  | true =>
    have eq : a = b := eq_of_beq h
    change (!(a == b)) = decide (a ≠ b)
    rw [h, _root_.decide_eq_false (fun neq => neq eq)]
    rfl

end OmegaChecks.InitPort.Alternatives
