module
import all Init.Grind.FieldNormNum

/-! Rational field normalization when the denominators are units. -/

open Lean.Grind Lean.Grind.Field.NormNum
namespace OmegaChecks.InitPort.Alternatives

attribute [local instance] Semiring.natCast Ring.intCast

private theorem productNonzero {α : Type u} [Field α] {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro zero
  have eq := congrArg (· * b⁻¹) zero
  rw [Semiring.mul_assoc, Field.mul_inv_cancel hb, Semiring.mul_one, Semiring.zero_mul] at eq
  exact ha eq

private theorem inverseProduct {α : Type u} [Field α] {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a*b)⁻¹ = a⁻¹*b⁻¹ := by
  symm
  apply Field.eq_inv_of_mul_eq_one
  rw [Semiring.mul_assoc, CommSemiring.mul_left_comm b⁻¹, Field.inv_mul_cancel hb,
      Semiring.mul_one, Field.inv_mul_cancel ha]

private theorem reduceFraction {α : Type u} [Field α] (x : α) {y z : α}
    (hy : y ≠ 0) (hz : z ≠ 0) : (x/z)/(y/z) = x/y := by
  rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv, Field.div_eq_mul_inv,
      inverseProduct hy (fun zero => hz (Field.inv_eq_zero_iff.mp zero)), Field.inv_inv,
      Field.div_eq_mul_inv, Semiring.mul_assoc, CommSemiring.mul_left_comm z⁻¹,
      Field.inv_mul_cancel hz, Semiring.mul_one]

public theorem Lean.Grind.Field.NormNum.nonzero_helper :
    type_of% (private_decl% @_root_.Lean.Grind.Field.NormNum.nonzero_helper) := by
  intro α _ z n m hn hm zero
  obtain ⟨k, eq⟩ := Nat.gcd_dvd_right z.natAbs (n*m)
  have projected := congrArg (Nat.cast (R := α)) eq
  rw [Semiring.natCast_mul, Semiring.natCast_mul, zero, Semiring.zero_mul] at projected
  exact productNonzero hn hm projected

private theorem normalizedRatio {α : Type u} [Field α] (z : Int) (n m : Nat)
    (hn : (n : α) ≠ 0) (hm : (m : α) ≠ 0) :
    ((z / (z.natAbs.gcd (n*m) : Int) : Int) : α) / ((n*m/(z.natAbs.gcd (n*m)) : Nat) : α) =
      (z : α) / ((n*m : Nat) : α) := by
  have gcdNZ : (z.natAbs.gcd (n*m) : α) ≠ 0 :=
    (private_decl% _root_.Lean.Grind.Field.NormNum.nonzero_helper) hn hm
  have prodNZ : ((n*m : Nat) : α) ≠ 0 := by
    rw [Semiring.natCast_mul]
    exact productNonzero hn hm
  have gcdIntNZ : (((z.natAbs.gcd (n*m) : Nat) : Int) : α) ≠ 0 := by
    rwa [Ring.intCast_natCast]
  rw [Field.intCast_div_of_dvd (private_decl% _root_.Lean.Grind.Field.NormNum.dvd_helper₁) gcdIntNZ,
      Field.natCast_div_of_dvd (private_decl% _root_.Lean.Grind.Field.NormNum.dvd_helper₂) gcdNZ,
      Ring.intCast_natCast, reduceFraction _ prodNZ gcdNZ]

public theorem Lean.Grind.Field.NormNum.ofRat_add' : type_of% @_root_.Lean.Grind.Field.NormNum.ofRat_add' := by
  intro α _ a b ha hb
  rw [ofRat, ofRat, ofRat, Rat.num_add, Rat.den_add, normalizedRatio _ _ _ ha hb,
      Semiring.natCast_mul, Ring.intCast_add, Ring.intCast_mul, Ring.intCast_mul,
      Ring.intCast_natCast, Ring.intCast_natCast, Field.add_div hb, Field.div_mul, Field.div_add ha,
      Field.div_eq_mul_inv, Field.div_eq_mul_inv, Field.div_eq_mul_inv, inverseProduct ha hb,
      CommSemiring.mul_comm (a.den : α) (b.num : α), Semiring.mul_assoc]

public theorem Lean.Grind.Field.NormNum.ofRat_mul' : type_of% @_root_.Lean.Grind.Field.NormNum.ofRat_mul' := by
  intro α _ a b ha hb
  rw [ofRat, ofRat, ofRat, Rat.num_mul, Rat.den_mul, normalizedRatio _ _ _ ha hb,
      Semiring.natCast_mul, Ring.intCast_mul, Field.div_eq_mul_inv, inverseProduct ha hb,
      Field.div_eq_mul_inv, Field.div_eq_mul_inv, Semiring.mul_assoc, Semiring.mul_assoc,
      CommSemiring.mul_left_comm (b.num : α)]

private theorem ofRatZero {α : Type u} [Field α] : (ofRat 0 : α) = 0 := by
  change (Int.cast (R := α) 0) / (Nat.cast (R := α) 1) = 0
  rw [Field.div_eq_mul_inv, Ring.intCast_zero, Semiring.zero_mul]

private theorem ofRatOne {α : Type u} [Field α] : (ofRat 1 : α) = 1 := by
  change (Int.cast (R := α) 1) / (Nat.cast (R := α) 1) = 1
  rw [Field.div_eq_mul_inv, Ring.intCast_one, Semiring.natCast_one, Field.inv_one, Semiring.mul_one]

private theorem ofRatInverse {α : Type u} [Field α] [IsCharP α 0] (a : Rat) :
    (ofRat a⁻¹ : α) = (ofRat a)⁻¹ := by
  by_cases zero : a = 0
  · rw [zero, Rat.inv_zero, ofRatZero, Field.inv_zero]
  · apply Field.eq_inv_of_mul_eq_one
    rw [← _root_.Lean.Grind.Field.NormNum.ofRat_mul, Rat.inv_mul_cancel a zero, ofRatOne]

public theorem Lean.Grind.Field.NormNum.ofRat_div : type_of% @_root_.Lean.Grind.Field.NormNum.ofRat_div := by
  intro α _ _ a b
  rw [Rat.div_def, _root_.Lean.Grind.Field.NormNum.ofRat_mul, ofRatInverse, Field.div_eq_mul_inv]

public theorem Lean.Grind.Field.NormNum.ofRat_zpow : type_of% @_root_.Lean.Grind.Field.NormNum.ofRat_zpow := by
  intro α _ _ a n
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, Rat.zpow_natCast, Field.zpow_natCast, _root_.Lean.Grind.Field.NormNum.ofRat_npow]
  | negSucc n =>
    change ofRat (a ^ (-((n+1 : Nat) : Int))) = (ofRat a : α) ^ (-((n+1 : Nat) : Int))
    rw [Rat.zpow_neg, ofRatInverse, Field.zpow_neg, Rat.zpow_natCast, Field.zpow_natCast,
        _root_.Lean.Grind.Field.NormNum.ofRat_npow]

public theorem Lean.Grind.Field.NormNum.ofRat_npow' : type_of% @_root_.Lean.Grind.Field.NormNum.ofRat_npow' := by
  intro α _ a ha n
  have denominator (j : Nat) : (((a^j).den : Nat) : α) ≠ 0 := by
    rw [Rat.den_pow, Semiring.natCast_pow]
    induction j with
    | zero =>
      rw [Semiring.pow_zero]
      exact fun e => Field.zero_ne_one e.symm
    | succ j ih =>
      rw [Semiring.pow_succ]
      exact productNonzero ih ha
  induction n with
  | zero => rw [Rat.pow_zero, ofRatOne, Semiring.pow_zero]
  | succ n ih =>
    rw [Rat.pow_succ, _root_.Lean.Grind.Field.NormNum.ofRat_mul' (denominator n) ha, ih, Semiring.pow_succ]

end OmegaChecks.InitPort.Alternatives
