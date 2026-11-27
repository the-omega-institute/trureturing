module

public import Init.Data.Nat.ToString
import all Init.Data.Nat.ToString
import all Init.Data.Repr

namespace OmegaChecks.InitPort.Alternatives

public theorem Nat.isDigit_digitChar : type_of% @_root_.Nat.isDigit_digitChar := by
  intro n
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => simp [_root_.Nat.digitChar]
  | 10 | 11 | 12 | 13 | 14 | 15 => simp [_root_.Nat.digitChar]
  | n + 16 =>
    rw [decide_eq_false (by omega)]
    unfold _root_.Nat.digitChar
    repeat rw [ite_eq_right (by omega)]
    decide

public theorem Nat.isDigit_of_mem_toDigitsCore :
    type_of% (private_decl% @_root_.Nat.isDigit_of_mem_toDigitsCore) := by
  intro b cs c fuel a known base bound inside
  have digit (n : Nat) : (n % b).digitChar.isDigit = true :=
    (Nat.isDigit_digitChar (n := n % b)).trans (decide_eq_true (Nat.lt_of_lt_of_le (Nat.mod_lt n base) bound))
  induction fuel generalizing a cs with
  | zero => exact known inside
  | succ fuel ih =>
    have cons : c ∈ (a % b).digitChar :: cs → c.isDigit = true := by
      intro h
      cases h with
      | head => exact digit a
      | tail _ h => exact known h
    rw [Nat.toDigitsCore] at inside
    split at inside
    · exact cons inside
    · exact ih cons inside

public theorem Nat.isDigit_of_mem_toDigits : type_of% @_root_.Nat.isDigit_of_mem_toDigits := by
  intro b n c base bound member
  exact (private_decl% _root_.Nat.isDigit_of_mem_toDigitsCore) (fun h => by cases h) base bound member

public theorem Nat.underscore_not_in_toDigits : type_of% @_root_.Nat.underscore_not_in_toDigits := by
  intro n h
  have digit := _root_.Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) h
  exact Bool.noConfusion (show false = true from digit)

public theorem Nat.length_toDigits_le_iff : type_of% @_root_.Nat.length_toDigits_le_iff := by
  intro b n k base positive
  induction k generalizing n with
  | zero => exact False.elim (Nat.lt_irrefl 0 positive)
  | succ k ih =>
    if small : n < b then
      rw [Nat.toDigits_of_lt_base small]
      have bound : b ≤ b ^ (k+1) := by
        rw [Nat.pow_succ]
        exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.zero_lt_of_lt base))
      exact ⟨fun _ => Nat.lt_of_lt_of_le small bound, fun _ => Nat.succ_le_succ (Nat.zero_le k)⟩
    else
      rw [Nat.toDigits_of_base_le base (Nat.le_of_not_lt small), List.length_append]
      change (b.toDigits (n / b)).length + 1 ≤ k + 1 ↔ n < b ^ (k+1)
      cases k with
      | zero =>
        rw [Nat.pow_one]
        have nonempty := Nat.length_toDigits_pos (b := b) (n := n / b)
        exact ⟨fun le => False.elim ((Nat.not_le_of_lt nonempty) (Nat.le_of_succ_le_succ le)),
          fun lt => False.elim (small lt)⟩
      | succ k =>
        rw [Nat.pow_succ b (k+1)]
        exact Nat.succ_le_succ_iff.trans ((ih (n := n/b) (Nat.zero_lt_succ k)).trans
          (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt base)))

end OmegaChecks.InitPort.Alternatives
