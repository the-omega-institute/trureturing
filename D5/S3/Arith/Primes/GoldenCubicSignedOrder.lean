/- GID: D5/S3/Arith/Primes/GoldenCubicSignedOrder
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicSignedOrder
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Signed returns are exactly multiples of a positive quotient order, with explicit five-power periods. -/

import D5.S3.Arith.Primes.GoldenCubicBlockTailPeriodClosed
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Primes.GoldenCubicSignedOrder

/-- Only the two *global* signs, not all square roots of one in a
composite residue ring. At modulus one these two signs coincide. -/
private def signUnits (Q : ℕ) : Subgroup (ZMod Q)ˣ where
  carrier := {u | u = 1 ∨ u = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by intro a b ha hb; rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> simp
  inv_mem' := by intro u hu; rcases hu with rfl|rfl <;> simp

/-- Order of a unit modulo the global subgroup of two signs. -/
noncomputable def signedOrder (a Q : ℕ) (h : a.Coprime Q) : ℕ :=
  orderOf (QuotientGroup.mk' (signUnits Q) (ZMod.unitOfCoprime a h))

theorem signedOrder_dvd_iff (a Q n : ℕ) (h : a.Coprime Q) :
    signedOrder a Q h ∣ n ↔
      (a : ZMod Q)^n = 1 ∨ (a : ZMod Q)^n = -1 := by
  let u := ZMod.unitOfCoprime a h
  change orderOf (QuotientGroup.mk' (signUnits Q) u) ∣ n ↔ _
  rw [orderOf_dvd_iff_pow_eq_one, ← map_pow]
  change ((u^n : (ZMod Q)ˣ) : (ZMod Q)ˣ ⧸ signUnits Q) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  change u^n = 1 ∨ u^n = -1 ↔ _
  simp only [← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_one, Units.val_neg,
    ZMod.coe_unitOfCoprime, u]

theorem signedOrder_pos (a Q : ℕ) (hQ : 0 < Q) (h : a.Coprime Q) :
    0 < signedOrder a Q h := by
  let _ : NeZero Q := ⟨hQ.ne'⟩
  unfold signedOrder
  exact orderOf_pos (QuotientGroup.mk' (signUnits Q) (ZMod.unitOfCoprime a h))

/-- Including Q=1: the least positive signed return is the unit quotient
order, and every signed return is one of its multiples. -/
theorem signedOrder_isLeast (a Q : ℕ) (hQ : 0 < Q) (h : a.Coprime Q) :
    IsLeast {n : ℕ | 0 < n ∧ ((a : ZMod Q)^n = 1 ∨ (a : ZMod Q)^n = -1)}
      (signedOrder a Q h) := by
  refine ⟨⟨signedOrder_pos a Q hQ h, (signedOrder_dvd_iff a Q _ h).mp dvd_rfl⟩,?_⟩
  intro n hn
  exact Nat.le_of_dvd hn.1 ((signedOrder_dvd_iff a Q n h).mpr hn.2)

theorem signedOrder_mod_one (a : ℕ) (h : a.Coprime 1) :
    signedOrder a 1 h = 1 := by
  have hd := (signedOrder_dvd_iff a 1 1 h).mpr (Or.inl (Subsingleton.elim _ _))
  exact Nat.dvd_one.mp hd

theorem signedOrder_dvd_iff_modEq (a Q n : ℕ) (h : a.Coprime Q) :
    signedOrder a Q h ∣ n ↔
      (a : ℤ)^n ≡ 1 [ZMOD (Q:ℤ)] ∨ (a : ℤ)^n ≡ -1 [ZMOD (Q:ℤ)] := by
  rw [signedOrder_dvd_iff]
  rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
  norm_cast

/-- Over an odd prime power the two signs exhaust square roots of one.
This assertion is deliberately not made for composite moduli in general. -/
theorem odd_prime_power_square_one_iff (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x : ℤ) :
    ((x : ZMod (p^r))^2 = 1) ↔ (x : ZMod (p^r)) = 1 ∨ (x : ZMod (p^r)) = -1 := by
  constructor
  · intro hx
    have hZ : (((x-1)*(x+1) : ℤ) : ZMod (p^r)) = 0 := by
      rw [show (x-1)*(x+1) = x^2-1 by ring, Int.cast_sub, Int.cast_pow, Int.cast_one,
        hx, sub_self]
    have hprod := (ZMod.intCast_zmod_eq_zero_iff_dvd ((x-1)*(x+1)) (p^r)).mp hZ
    push_cast at hprod
    have hpZ : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
    have hn : ¬(p:ℤ) ∣ 2 := by
      intro hd
      have hd' : p ∣ 2 := by exact_mod_cast hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd')
    by_cases hm : (p:ℤ) ∣ x-1
    · have hnplus : ¬(p:ℤ) ∣ x+1 := fun H => hn (by
        have hs := dvd_sub H hm
        simpa only [show x+1-(x-1) = (2:ℤ) by ring] using hs)
      have hv := hpZ.pow_dvd_of_dvd_mul_right r hnplus hprod
      have hw : (((x-1:ℤ):ZMod (p^r))) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (x-1) (p^r)).mpr (by exact_mod_cast hv)
      left
      simpa only [Int.cast_sub, Int.cast_one, sub_eq_zero] using hw
    · have hv := hpZ.pow_dvd_of_dvd_mul_left r hm hprod
      have hw : (((x+1:ℤ):ZMod (p^r))) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (x+1) (p^r)).mpr (by exact_mod_cast hv)
      right
      simpa only [Int.cast_add, Int.cast_one, eq_neg_iff_add_eq_zero] using hw
  · rintro (h|h) <;> rw [h] <;> ring

theorem three_signedOrder_prime_power (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hc : (3:ℕ).Coprime (p^r)) :
    signedOrder 3 (p^r) hc = orderOf (9 : ZMod (p^r)) := by
  have h (n : ℕ) : signedOrder 3 (p^r) hc ∣ n ↔ orderOf (9 : ZMod (p^r)) ∣ n := by
    rw [signedOrder_dvd_iff, orderOf_dvd_iff_pow_eq_one]
    have hs := odd_prime_power_square_one_iff p r hp hp2 ((3:ℤ)^n)
    have h9 : ((3 : ZMod (p^r))^n)^2 = (9 : ZMod (p^r))^n := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    simpa only [Int.cast_pow, Int.cast_ofNat, Nat.cast_ofNat, h9] using hs.symm
  exact Nat.dvd_antisymm ((h _).mpr dvd_rfl) ((h _).mp dvd_rfl)

theorem signedOrder_three_mod_five_pow (r : ℕ) (h : (3:ℕ).Coprime (5^r)) :
    signedOrder 3 (5^r) h = if r = 0 then 1 else 2 * 5^(r-1) := by
  by_cases hr : r=0
  · subst r
    simp only [pow_zero, ite_true]
    exact signedOrder_mod_one 3 _
  · rw [ite_eq_right hr, three_signedOrder_prime_power 5 r Nat.prime_five (by decide) h,
      GoldenCubicBlockTailPeriodClosed.orderOf_nine_prime_power 5 r Nat.prime_five
        (by decide) (by decide) (by omega)]
    have ho : orderOf (9 : ZMod 5) = 2 :=
      orderOf_eq_prime (p := 2) (by decide) (by decide)
    have hv : padicValNat 5 (3^(5-1)-1) = 1 := by
      let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      change padicValNat 5 80 = 1
      rw [show (80:ℕ) = 5*16 by decide, padicValNat.mul (by decide) (by decide),
        padicValNat.self (by decide), padicValNat.eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 16),
        add_zero]
    rw [ho, hv]

private theorem signedOrder_three_mod91_or_mod7 (Q T : ℕ) (hQ : 0 < Q) (hc : (3:ℕ).Coprime Q)
    (hT : 0 < T) (hTret : (3 : ZMod Q)^T = 1 ∨ (3 : ZMod Q)^T = -1)
    (hother : ∀ n < T, 0 < n → ¬((3 : ZMod Q)^n = 1 ∨ (3 : ZMod Q)^n = -1)) :
    signedOrder 3 Q hc = T := by
  have hs := signedOrder_pos 3 Q hQ hc
  have hle := Nat.le_of_dvd hT ((signedOrder_dvd_iff 3 Q T hc).mpr hTret)
  have hr := (signedOrder_dvd_iff 3 Q (signedOrder 3 Q hc) hc).mp dvd_rfl
  exact le_antisymm hle (Nat.le_of_not_lt (fun H => hother _ H hs hr))

/-- A concrete mixed-sign regression: 27 has square one mod 91, but neither global sign. -/
theorem mixed_sign_mod91 :
    (3:ZMod 91)^(3:ℕ) ≠ 1 ∧ (3:ZMod 91)^(3:ℕ) ≠ -1 ∧
    (9:ZMod 91)^(3:ℕ) = 1 := by decide

theorem signedOrder_three_mod91 (h : (3:ℕ).Coprime 91) : signedOrder 3 91 h = 6 := by
  apply signedOrder_three_mod91_or_mod7 91 6 (by decide) h (by decide) (by decide)
  intro n hn hn0
  interval_cases n <;> decide

theorem signedOrder_three_mod7 (h : (3:ℕ).Coprime 7) : signedOrder 3 7 h = 3 := by
  apply signedOrder_three_mod91_or_mod7 7 3 (by decide) h (by decide) (by decide)
  intro n hn hn0
  interval_cases n <;> decide

end D5.S3.Arith.Primes.GoldenCubicSignedOrder
