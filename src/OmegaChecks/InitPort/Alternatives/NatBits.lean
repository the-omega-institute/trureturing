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

public theorem Nat.exists_testBit_ne_of_ne : type_of% @_root_.Nat.exists_testBit_ne_of_ne := by
  intro x y neq
  induction y using Nat.div2Induction generalizing x with
  | ind y prior =>
    cases Nat.eq_zero_or_pos y with
    | inl e =>
      subst y
      obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero neq
      exact ⟨i, fun h => Bool.noConfusion (hi.symm.trans (h.trans (Nat.zero_testBit i)))⟩
    | inr ypos =>
      by_cases low : x % 2 = y % 2
      · have different : x / 2 ≠ y / 2 := fun equal => neq <|
          (Nat.div_add_mod x 2).symm.trans <| (congrArg (fun q => 2 * q + x % 2) equal).trans <|
            (congrArg (fun r => 2 * (y / 2) + r) low).trans (Nat.div_add_mod y 2)
        obtain ⟨i, hi⟩ := prior ypos different
        exact ⟨i+1, fun h => hi ((Nat.testBit_succ x i).symm.trans (h.trans (Nat.testBit_succ y i)))⟩
      · refine ⟨0, fun h => low ?_⟩
        rw [Nat.testBit_zero, Nat.testBit_zero] at h
        cases Nat.mod_two_eq_zero_or_one x with
        | inl hx =>
          cases Nat.mod_two_eq_zero_or_one y with
          | inl hy => exact hx.trans hy.symm
          | inr hy => rw [hx, hy] at h; contradiction
        | inr hx =>
          cases Nat.mod_two_eq_zero_or_one y with
          | inl hy => rw [hx, hy] at h; contradiction
          | inr hy => exact hx.trans hy.symm

public theorem Nat.eq_of_testBit_eq : type_of% @_root_.Nat.eq_of_testBit_eq := by
  intro x y bits
  by_cases equal : x = y
  · exact equal
  · obtain ⟨i, hi⟩ := Nat.exists_testBit_ne_of_ne equal
    exact False.elim (hi (bits i))

public theorem Nat.shiftLeft_eq_zero_iff : type_of% @_root_.Nat.shiftLeft_eq_zero_iff := by
  intro a n
  rw [Nat.shiftLeft_eq]
  constructor
  · intro zero
    cases Nat.mul_eq_zero.mp zero with
    | inl h => exact h
    | inr h => exact False.elim (Nat.ne_of_gt (Nat.pow_pos Nat.zero_lt_two) h)
  · intro h
    subst a
    exact Nat.zero_mul _

end OmegaChecks.InitPort.Alternatives
