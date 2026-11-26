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

public theorem Rat.divInt_eq_divInt_iff : type_of% @_root_.Rat.divInt_eq_divInt_iff := by
  intro d₁ d₂ n₁ n₂ z₁ z₂
  have transpose (a b : Int) : a = -b ↔ -a = b :=
    ⟨fun h => (congrArg Neg.neg h).trans (Int.neg_neg b),
     fun h => (Int.neg_neg a).symm.trans (congrArg Neg.neg h)⟩
  cases d₁ with
  | ofNat d₁ =>
    cases d₂ with
    | ofNat d₂ =>
      exact Rat.mkRat_eq_iff (fun h => z₁ (congrArg Int.ofNat h)) (fun h => z₂ (congrArg Int.ofNat h))
    | negSucc d₂ =>
      change Rat.divInt n₁ (Int.ofNat d₁) = Rat.divInt n₂ (-(Int.ofNat (d₂+1))) ↔ _
      rw [Rat.divInt_neg']
      change mkRat n₁ d₁ = mkRat (-n₂) (d₂+1) ↔ _
      apply (Rat.mkRat_eq_iff (fun h => z₁ (congrArg Int.ofNat h)) (Nat.succ_ne_zero _)).trans
      rw [Int.neg_mul]
      change _ ↔ n₁ * (-(Int.ofNat (d₂+1))) = n₂ * Int.ofNat d₁
      rw [Int.mul_neg]
      exact transpose _ _
  | negSucc d₁ =>
    cases d₂ with
    | ofNat d₂ =>
      change Rat.divInt n₁ (-(Int.ofNat (d₁+1))) = Rat.divInt n₂ (Int.ofNat d₂) ↔ _
      rw [Rat.divInt_neg']
      change mkRat (-n₁) (d₁+1) = mkRat n₂ d₂ ↔ _
      apply (Rat.mkRat_eq_iff (Nat.succ_ne_zero _) (fun h => z₂ (congrArg Int.ofNat h))).trans
      rw [Int.neg_mul]
      change _ ↔ n₁ * Int.ofNat d₂ = n₂ * (-(Int.ofNat (d₁+1)))
      rw [Int.mul_neg]
      exact (transpose _ _).symm
    | negSucc d₂ =>
      change Rat.divInt n₁ (-(Int.ofNat (d₁+1))) = Rat.divInt n₂ (-(Int.ofNat (d₂+1))) ↔ _
      rw [Rat.divInt_neg', Rat.divInt_neg']
      change mkRat (-n₁) (d₁+1) = mkRat (-n₂) (d₂+1) ↔ _
      apply (Rat.mkRat_eq_iff (Nat.succ_ne_zero _) (Nat.succ_ne_zero _)).trans
      rw [Int.neg_mul, Int.neg_mul]
      change _ ↔ n₁ * (-(Int.ofNat (d₂+1))) = n₂ * (-(Int.ofNat (d₁+1)))
      rw [Int.mul_neg, Int.mul_neg]
      rfl

public theorem Rat.divInt_self' : type_of% @_root_.Rat.divInt_self' := by
  intro n hn
  change Rat.divInt n n = Rat.divInt 1 1
  apply (Rat.divInt_eq_divInt_iff hn (by decide)).mpr
  rw [Int.mul_one, Int.one_mul]

public theorem Rat.mul_inv_cancel : type_of% @_root_.Rat.mul_inv_cancel := by
  intro a ha
  have numerator : a.num ≠ 0 := fun h => ha (Rat.num_eq_zero.mp h)
  have denominator : (a.den : Int) ≠ 0 := fun h => a.den_nz (Int.ofNat.inj h)
  calc
    a * a⁻¹ = Rat.divInt a.num a.den * a⁻¹ := congrArg (· * a⁻¹) (Rat.num_divInt_den a).symm
    _ = Rat.divInt (a.num * (a.den : Int)) ((a.den : Int) * a.num) := by
      rw [Rat.inv_def, Rat.divInt_mul_divInt]
    _ = 1 := by
      rw [Int.mul_comm a.num]
      exact Rat.divInt_self' (Int.mul_ne_zero denominator numerator)

end OmegaChecks.InitPort.Alternatives
