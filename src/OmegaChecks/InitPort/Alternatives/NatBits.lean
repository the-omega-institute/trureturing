module
public import Init.Data.Nat.Bitwise.Lemmas

namespace OmegaChecks.InitPort.Alternatives

public theorem Bool.beq_eq_decide_eq : type_of% @_root_.Bool.beq_eq_decide_eq := by
  intro α _ _ _ a b
  cases h : a == b with
  | false => exact (decide_eq_false (ne_of_beq_false h)).symm
  | true => exact (decide_eq_true (eq_of_beq h)).symm

public theorem Nat.mod_two_bne_zero : type_of% @_root_.Nat.mod_two_bne_zero := by
  intro a
  cases Nat.mod_two_eq_zero_or_one a with
  | inl h => rw [h]; rfl
  | inr h => rw [h]; rfl

public theorem Nat.testBit_zero : type_of% @_root_.Nat.testBit_zero := by
  intro x
  change (1 &&& x != 0) = decide (x % 2 = 1)
  rw [Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero]
  rfl

public theorem Nat.testBit_eq_decide_div_mod_eq : type_of% @_root_.Nat.testBit_eq_decide_div_mod_eq := by
  intro i x
  induction i generalizing x with
  | zero =>
    rw [Nat.testBit_zero, Nat.pow_zero, Nat.div_one]
  | succ i ih =>
    rw [Nat.testBit_succ, ih, Nat.div_div_eq_div_mul, Nat.mul_comm 2, Nat.pow_succ]

end OmegaChecks.InitPort.Alternatives
