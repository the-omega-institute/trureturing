module
public import Init.Data.Nat.Bitwise.Lemmas
public import Init.Data.Nat.Power2.Bitwise
import all Init.Data.Nat.Power2.Basic

namespace OmegaChecks.InitPort.Alternatives

public theorem Bool.beq_eq_decide_eq : type_of% @_root_.Bool.beq_eq_decide_eq := by
  intro α inst law dec a b
  cases dec a b with
  | isTrue h => cases h; exact law.rfl
  | isFalse h =>
    cases eq : a == b with
    | false => rfl
    | true => exact False.elim (h (law.eq_of_beq eq))

public theorem Bool.beq_comm : type_of% @_root_.Bool.beq_comm := by
  intro α eq law a b
  apply Bool.eq_iff_iff.mpr
  exact ⟨fun h => law.eq_of_beq h ▸ law.rfl, fun h => law.eq_of_beq h ▸ law.rfl⟩

public theorem false_eq_decide_iff : type_of% @_root_.false_eq_decide_iff :=
  fun {_} _ => ⟨fun h => of_decide_eq_false h.symm, fun h => (decide_eq_false h).symm⟩

public theorem Bool.not_ite_eq_false_eq_false : type_of% @_root_.Bool.not_ite_eq_false_eq_false := by
  intro p dec b c
  cases dec with
  | isTrue _ => change (¬ b = false) ↔ b = true; cases b <;> decide
  | isFalse _ => change (¬ c = false) ↔ c = true; cases c <;> decide

public theorem Bool.not_ite_eq_true_eq_false : type_of% @_root_.Bool.not_ite_eq_true_eq_false := by
  intro p dec b c
  cases dec with
  | isTrue _ => change (¬ b = true) ↔ b = false; cases b <;> decide
  | isFalse _ => change (¬ c = false) ↔ c = true; cases c <;> decide

public theorem Bool.not_ite_eq_false_eq_true : type_of% @_root_.Bool.not_ite_eq_false_eq_true := by
  intro p dec b c
  cases dec with
  | isTrue _ => change (¬ b = false) ↔ b = true; cases b <;> decide
  | isFalse _ => change (¬ c = true) ↔ c = false; cases c <;> decide

public theorem Bool.decide_and : type_of% @_root_.Bool.decide_and := by
  intro p q dpq dp dq
  cases dp with
  | isFalse hp =>
    exact decide_eq_false fun h => hp h.1
  | isTrue hp =>
    cases dq with
    | isFalse hq => exact decide_eq_false fun h => hq h.2
    | isTrue hq => exact decide_eq_true ⟨hp, hq⟩

public theorem Bool.decide_or : type_of% @_root_.Bool.decide_or := by
  intro p q dpq dp dq
  cases dp with
  | isTrue hp => exact decide_eq_true (Or.inl hp)
  | isFalse hp =>
    cases dq with
    | isTrue hq => exact decide_eq_true (Or.inr hq)
    | isFalse hq => exact decide_eq_false fun h => h.elim hp hq

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

public theorem Nat.or_zero : type_of% @_root_.Nat.or_zero := by
  intro x
  apply _root_.Nat.eq_of_testBit_eq
  intro i
  rw [_root_.Nat.testBit_or, _root_.Nat.zero_testBit]
  cases x.testBit i <;> rfl

public theorem Nat.zero_or : type_of% @_root_.Nat.zero_or := by
  intro x
  apply _root_.Nat.eq_of_testBit_eq
  intro i
  rw [_root_.Nat.testBit_or, _root_.Nat.zero_testBit]
  rfl

public theorem Nat.and_one_is_mod : type_of% @_root_.Nat.and_one_is_mod :=
  fun x => Nat.and_two_pow_sub_one_eq_mod x 1

public theorem Nat.or_mod_two_eq_one : type_of% @_root_.Nat.or_mod_two_eq_one := by
  intro a b
  apply Nat.mod_two_eq_one_iff_testBit_zero.trans
  rw [Nat.testBit_or]
  exact Bool.or_eq_true_iff.trans (or_congr Nat.mod_two_eq_one_iff_testBit_zero.symm Nat.mod_two_eq_one_iff_testBit_zero.symm)

public theorem Nat.left_le_or : type_of% @_root_.Nat.left_le_or := by
  intro n m
  refine Nat.le_of_testBit fun i bit => ?_
  rw [Nat.testBit_or, bit, Bool.true_or]

public theorem Nat.right_le_or : type_of% @_root_.Nat.right_le_or := by
  intro n m
  refine Nat.le_of_testBit fun i bit => ?_
  rw [Nat.testBit_or, bit, Bool.or_true]

private theorem highestBitAfterSub {n : Nat} (nonzero : n ≠ 0) (hne : n ≠ 2 ^ n.log2) :
    (n &&& (n - 1)).testBit n.log2 = true := by
  have bounds := (_root_.Nat.log2_eq_iff (k := n.log2) nonzero).mp rfl
  have lower := Nat.lt_of_le_of_ne bounds.1 (Ne.symm hne)
  have positive := Nat.two_pow_pos n.log2
  have previous : n - 1 ≠ 0 := by omega
  have log : (n - 1).log2 = n.log2 := (_root_.Nat.log2_eq_iff previous).mpr
    ⟨by omega, Nat.lt_of_le_of_lt (Nat.sub_le ..) bounds.2⟩
  rw [Nat.testBit_and, Nat.testBit_log2 nonzero, ← log, Nat.testBit_log2 previous]
  rfl

public theorem Nat.and_sub_one_testBit_log2 : type_of% @_root_.Nat.and_sub_one_testBit_log2 :=
  fun {_} hn hpow => highestBitAfterSub hn fun h => hpow ⟨_, h⟩

public theorem Nat.and_sub_one_eq_zero_iff_isPowerOfTwo :
    type_of% @_root_.Nat.and_sub_one_eq_zero_iff_isPowerOfTwo := by
  intro n hn
  constructor
  · intro h
    by_cases hp : n = 2 ^ n.log2
    · exact ⟨n.log2, hp⟩
    · have bit := highestBitAfterSub hn hp
      rw [h, Nat.zero_testBit] at bit
      contradiction
  · rintro ⟨k, rfl⟩
    exact (Nat.and_two_pow_sub_one_eq_mod ..).trans (Nat.mod_self _)

public theorem Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo :
    type_of% @_root_.Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo := by
  intro n
  constructor
  · rintro ⟨hn, h⟩
    exact (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hn).mp h
  · intro h
    have hn : n ≠ 0 := fun e => Nat.not_isPowerOfTwo_zero (e ▸ h)
    exact ⟨hn, (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hn).mpr h⟩

end OmegaChecks.InitPort.Alternatives
