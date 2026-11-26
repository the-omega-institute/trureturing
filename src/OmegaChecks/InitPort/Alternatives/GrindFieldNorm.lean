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

end OmegaChecks.InitPort.Alternatives
