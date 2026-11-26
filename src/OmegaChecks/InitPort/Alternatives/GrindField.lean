module
import all Init.Grind.Ring.Field
import all Init.Grind.Ordered.Ring

/-! Field inverses, integer casts, and signs derived from the algebraic structure. -/

open Lean.Grind
namespace OmegaChecks.InitPort.Alternatives

public theorem Lean.Grind.Field.eq_inv_of_mul_eq_one :
    type_of% @_root_.Lean.Grind.Field.eq_inv_of_mul_eq_one := by
  intro α _ a b one
  have nz : b ≠ 0 := fun zero => Field.zero_ne_one ((Semiring.mul_zero a).symm.trans (zero ▸ one))
  have h := congrArg (fun t : α => t * b⁻¹) one
  rwa [Semiring.mul_assoc, Field.mul_inv_cancel nz, Semiring.mul_one, Semiring.one_mul] at h

public theorem Lean.Grind.Field.inv_inv : type_of% @_root_.Lean.Grind.Field.inv_inv := by
  intro α _ a
  have back := Field.zpow_neg a (-1 : Int)
  change a ^ (1 : Int) = (a ^ (-1 : Int))⁻¹ at back
  rw [Field.zpow_one, Field.zpow_neg_one] at back
  exact back.symm

public theorem Lean.Grind.Field.inv_eq_zero_iff : type_of% @_root_.Lean.Grind.Field.inv_eq_zero_iff := by
  intro α _ a
  constructor
  · intro h
    have e := congrArg Inv.inv h
    rwa [Field.inv_inv, Field.inv_zero] at e
  · rintro rfl
    exact Field.inv_zero

public theorem Lean.Grind.Field.zero_eq_inv_iff : type_of% @_root_.Lean.Grind.Field.zero_eq_inv_iff := by
  intro α _ a
  exact ⟨fun h => (Field.inv_eq_zero_iff.mp h.symm).symm, fun h => (Field.inv_eq_zero_iff.mpr h.symm).symm⟩

section
attribute [local instance] Semiring.natCast Ring.intCast

public theorem Lean.Grind.Field.intCast_div_of_dvd : type_of% @_root_.Lean.Grind.Field.intCast_div_of_dvd := by
  intro α _ x y divides nz
  obtain ⟨z, rfl⟩ := divides
  have hy : y ≠ 0 := fun h => nz (h ▸ Ring.intCast_zero)
  rw [Int.mul_ediv_cancel_left _ hy, Ring.intCast_mul, CommSemiring.mul_comm, Field.div_eq_mul_inv,
      Semiring.mul_assoc, Field.mul_inv_cancel nz, Semiring.mul_one]

public theorem Lean.Grind.Field.natCast_div_of_dvd : type_of% @_root_.Lean.Grind.Field.natCast_div_of_dvd := by
  intro α _ x y divides nz
  obtain ⟨z, rfl⟩ := divides
  have hy : y ≠ 0 := fun h => nz (h ▸ Semiring.natCast_zero)
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hy), Semiring.natCast_mul, CommSemiring.mul_comm,
      Field.div_eq_mul_inv, Semiring.mul_assoc, Field.mul_inv_cancel nz, Semiring.mul_one]

set_option linter.defProp false in
@[instance_reducible] public def Lean.Grind.Field.noNatZeroDivisors.ofIsCharPZero :
    type_of% @_root_.Lean.Grind.Field.noNatZeroDivisors.ofIsCharPZero := by
  intro α _ _
  apply NoNatZeroDivisors.mk'
  intro k a nz zero
  rw [Semiring.nsmul_eq_ofNat_mul, Semiring.ofNat_eq_natCast] at zero
  have h := congrArg (fun t : α => (k : α)⁻¹ * t) zero
  rwa [← Semiring.mul_assoc, Field.inv_mul_cancel (Field.natCast_ne_zero nz), Semiring.one_mul,
      Semiring.mul_zero] at h

public theorem Lean.Grind.Ring.intCast_eq_ofNat_of_nonneg :
    type_of% @_root_.Lean.Grind.Ring.intCast_eq_ofNat_of_nonneg := by
  intro α _ x h
  cases x with
  | ofNat n => exact (Ring.intCast_natCast ..).trans (Semiring.ofNat_eq_natCast n).symm
  | negSucc n => contradiction

public theorem Lean.Grind.Ring.intCast_eq_ofNat_of_nonpos :
    type_of% @_root_.Lean.Grind.Ring.intCast_eq_ofNat_of_nonpos := by
  intro α _ x h
  cases x with
  | ofNat n =>
    cases n with
    | zero => exact Ring.intCast_zero.trans AddCommGroup.neg_zero.symm
    | succ n => contradiction
  | negSucc n =>
    change Int.cast (R := α) (-((n+1 : Nat) : Int)) = -OfNat.ofNat (n+1)
    rw [Ring.intCast_neg, Ring.intCast_natCast, Semiring.ofNat_eq_natCast (n+1)]

public theorem Lean.Grind.OrderedRing.pos_intCast_of_pos :
    type_of% @_root_.Lean.Grind.OrderedRing.pos_intCast_of_pos := by
  intro α _ _ _ _ _ _ x h
  cases x with
  | ofNat n =>
    change 0 < Int.cast (R := α) (n : Int)
    rw [Ring.intCast_natCast]
    exact OrderedRing.pos_natCast_of_pos n (Int.natCast_pos.mp h)
  | negSucc n => exact False.elim (Int.not_lt_of_ge (Int.le_of_lt (Int.negSucc_lt_zero n)) h)

public theorem Lean.Grind.OrderedRing.nonneg_intCast_of_nonneg :
    type_of% @_root_.Lean.Grind.OrderedRing.nonneg_intCast_of_nonneg := by
  intro α _ _ _ _ _ _ x h
  cases x with
  | ofNat n =>
    change 0 ≤ Int.cast (R := α) (n : Int)
    rw [Ring.intCast_natCast]
    exact OrderedRing.natCast_nonneg
  | negSucc n => exact False.elim (Int.not_le_of_gt (Int.negSucc_lt_zero n) h)

public theorem Lean.Grind.OrderedRing.neg_intCast_of_neg :
    type_of% @_root_.Lean.Grind.OrderedRing.neg_intCast_of_neg := by
  intro α _ _ _ _ _ _ x h
  have pos := OrderedRing.pos_intCast_of_pos (R := α) (-x) (Int.neg_pos_of_neg h)
  rw [Ring.intCast_neg] at pos
  exact OrderedAdd.neg_pos_iff.mp pos

public theorem Lean.Grind.OrderedRing.nonpos_intCast_of_nonpos :
    type_of% @_root_.Lean.Grind.OrderedRing.nonpos_intCast_of_nonpos := by
  intro α _ _ _ _ _ _ x h
  have pos := OrderedRing.nonneg_intCast_of_nonneg (R := α) (-x) (Int.neg_nonneg_of_nonpos h)
  rw [Ring.intCast_neg] at pos
  exact OrderedAdd.neg_nonneg_iff.mp pos

end

public theorem Lean.Grind.Ring.neg_ofNat_sub : type_of% @_root_.Lean.Grind.Ring.neg_ofNat_sub := by
  intro α _ x y h
  rw [Ring.ofNat_sub h, AddCommGroup.neg_sub]

public theorem Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos :
    type_of% @_root_.Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos := by
  intro α _ _ _ _ _ _ a b neg pos
  have h := OrderedRing.mul_pos (OrderedAdd.neg_pos_iff.mpr neg) pos
  rw [Ring.neg_mul] at h
  exact OrderedAdd.neg_pos_iff.mp h

public theorem Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg :
    type_of% @_root_.Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg := by
  intro α _ _ _ _ _ _ a b pos neg
  have h := OrderedRing.mul_pos pos (OrderedAdd.neg_pos_iff.mpr neg)
  rw [Ring.mul_neg] at h
  exact OrderedAdd.neg_pos_iff.mp h

public theorem Lean.Grind.OrderedRing.sq_pos : type_of% @_root_.Lean.Grind.OrderedRing.sq_pos := by
  intro α _ _ _ _ _ _ a nz
  rw [Semiring.pow_two]
  cases Std.le_total (a := 0) (b := a) with
  | inl le =>
    have pos := Std.lt_iff_le_and_not_ge.mpr ⟨le, fun ge => nz (Std.le_antisymm ge le)⟩
    exact OrderedRing.mul_pos pos pos
  | inr le =>
    have neg := Std.lt_iff_le_and_not_ge.mpr ⟨le, fun ge => nz (Std.le_antisymm le ge)⟩
    exact OrderedRing.mul_pos_of_neg_of_neg neg neg

end OmegaChecks.InitPort.Alternatives
