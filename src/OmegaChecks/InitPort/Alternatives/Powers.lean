module
import all Init.Data.Rat.Basic
import all Init.Data.Rat.Lemmas

namespace OmegaChecks.InitPort.Alternatives

public theorem Nat.gcd_mul_right_right_of_gcd_eq_one : type_of% @_root_.Nat.gcd_mul_right_right_of_gcd_eq_one := by
  intro n m k coprime
  apply Nat.dvd_antisymm
  · have divides := Nat.gcd_mul_right_dvd_mul_gcd n m k
    rw [coprime, Nat.one_mul] at divides
    exact divides
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left n k) (Nat.dvd_mul_left_of_dvd (Nat.gcd_dvd_right n k) m)

public theorem Nat.pow_lt_pow_left : type_of% @_root_.Nat.pow_lt_pow_left := by
  intro a b n lt nonzero
  cases n with
  | zero => exact False.elim (nonzero rfl)
  | succ n =>
    induction n with
    | zero =>
      change a ^ 1 < b ^ 1
      rw [Nat.pow_one, Nat.pow_one]
      exact lt
    | succ n ih =>
      rw [Nat.pow_succ a, Nat.pow_succ b]
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_of_lt lt))
        (Nat.mul_lt_mul_of_pos_right (ih (Nat.succ_ne_zero _)) (Nat.lt_of_le_of_lt (Nat.zero_le _) lt))

public theorem Rat.pow._proof_1 : type_of% @_root_.Rat.pow._proof_1 :=
  fun q _ => Nat.ne_of_gt (Nat.pow_pos (Nat.pos_of_ne_zero q.den_nz))

public theorem Rat.pow_def._proof_1 : type_of% @_root_.Rat.pow_def._proof_1 :=
  Rat.pow._proof_1

end OmegaChecks.InitPort.Alternatives
