import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega

/-!
# Actual multiplicative order modulo a power quotient

Source preparation only: this candidate has not been elaborated or kernel checked.
The target is the actual multiplicative group order, represented by `orderOf` in
`ZMod`'s multiplicative monoid; the modulus-one case is included. Quotient
divisibility supplies the return exponent. A size bound excludes returns at
prime-divided exponents when `k >= 2`. At the equal-gap boundary `k = 1`, the
quotient is `u ^ a - 1` and the claimed order is `a` rather than `2 * a`.

An application to a full-period nonunit implication requires a separately proved
action and seed/divisibility bridge. No such dynamics or physical theorem is
asserted here.
-/

namespace D5.S3.Arith.Congruence.PowerQuotientOrder

private theorem pow_zmod_eq_one_iff_dvd (u N e : ℕ) (hu : 0 < u) :
    (u : ZMod N) ^ e = 1 ↔ N ∣ u ^ e - 1 := by
  have hone : 1 ≤ u ^ e := Nat.one_le_pow e u hu
  constructor
  · intro h
    have hm : u ^ e ≡ 1 [MOD N] :=
      (ZMod.natCast_eq_natCast_iff (u ^ e) 1 N).mp
        (by simpa only [Nat.cast_pow, Nat.cast_one] using h)
    exact hm.symm.dvd'
  · intro h
    have hm : 1 ≡ u ^ e [MOD N] := (Nat.modEq_iff_dvd' hone).mpr h
    have hz := (ZMod.natCast_eq_natCast_iff (u ^ e) 1 N).mpr hm.symm
    simpa only [Nat.cast_pow, Nat.cast_one] using hz

private theorem square_sub_one_factor (t : ℕ) (ht : 1 ≤ t) :
    (t + 1) * (t - 1) = t ^ 2 - 1 := by
  simpa only [geom_sum_two] using (geom_sum_mul_of_one_le ht 2)

private theorem denominator_dvd (u a k : ℕ) (hu : 0 < u) :
    u ^ a + 1 ∣ u ^ (2 * a * k) - 1 := by
  have hbase : u ^ a + 1 ∣ (u ^ a) ^ 2 - 1 :=
    ⟨u ^ a - 1, (square_sub_one_factor (u ^ a) (Nat.one_le_pow a u hu)).symm⟩
  have hpow : (u ^ a) ^ 2 - 1 ∣ (u ^ a) ^ (2 * k) - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one (u ^ a) ⟨k, rfl⟩
  have he : a * (2 * k) = 2 * a * k := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  simpa only [← pow_mul, he] using hbase.trans hpow

private theorem quotient_at_one (u a : ℕ) (hu : 0 < u) :
    (u ^ (2 * a * 1) - 1) / (u ^ a + 1) = u ^ a - 1 := by
  have he : 2 * a * 1 = a * 2 := by
    simp only [Nat.mul_one, Nat.mul_comm]
  rw [he, pow_mul, ← square_sub_one_factor (u ^ a) (Nat.one_le_pow a u hu)]
  exact Nat.mul_div_cancel_left _ (by omega)

private theorem power_sub_one_order (u a : ℕ) (hu : 2 ≤ u) (ha : 0 < a) :
    orderOf (u : ZMod (u ^ a - 1)) = a := by
  have hu0 : 0 < u := by omega
  refine (orderOf_eq_iff ha).mpr ⟨?_, ?_⟩
  · exact (pow_zmod_eq_one_iff_dvd u (u ^ a - 1) a hu0).mpr (dvd_refl _)
  · intro j hja hj hreturn
    have hdiv : u ^ a - 1 ∣ u ^ j - 1 :=
      (pow_zmod_eq_one_iff_dvd u (u ^ a - 1) j hu0).mp hreturn
    have hone : 1 < u ^ j := Nat.one_lt_pow (Nat.ne_of_gt hj) (by omega)
    have hpow : u ^ j < u ^ a := Nat.pow_lt_pow_right (by omega) hja
    have hpos : 0 < u ^ j - 1 := by omega
    have hsmall : u ^ j - 1 < u ^ a - 1 := by omega
    exact (Nat.not_le_of_lt hsmall) (Nat.le_of_dvd hpos hdiv)

private theorem quotient_half_bound (u a k : ℕ)
    (hu : 2 ≤ u) (ha : 0 < a) (hk : 2 ≤ k) :
    u ^ (a * k) ≤ (u ^ (2 * a * k) - 1) / (u ^ a + 1) := by
  have hu0 : 0 < u := by omega
  have ht : 2 ≤ u ^ a := hu.trans (Nat.le_self_pow (Nat.ne_of_gt ha) u)
  have hdouble : u ^ a + u ^ a ≤ (u ^ a) ^ 2 := by
    simpa only [two_mul, pow_two] using (Nat.mul_le_mul_right (u ^ a) ht)
  have hsquare : u ^ a + 1 < (u ^ a) ^ 2 := by omega
  have hmon : (u ^ a) ^ 2 ≤ (u ^ a) ^ k :=
    Nat.pow_le_pow_right (Nat.pow_pos hu0) hk
  have hDX : u ^ a + 1 < u ^ (a * k) := by
    rw [pow_mul]
    exact hsquare.trans_le hmon
  have hXpos : 0 < u ^ (a * k) := Nat.pow_pos hu0
  have hprod : u ^ (a * k) * (u ^ a + 1) < u ^ (2 * a * k) := by
    have he : 2 * a * k = (a * k) * 2 := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    simpa only [he, pow_mul, pow_two] using
      (Nat.mul_lt_mul_of_pos_left hDX hXpos)
  exact (Nat.le_div_iff_mul_le (by omega : 0 < u ^ a + 1)).mpr (by omega)

/-- Exact order modulo the natural quotient, including the modulus-one boundary. -/
theorem power_quotient_order (u a k : ℕ) (hu : 2 ≤ u) (ha : 0 < a) (hk : 0 < k) :
    orderOf (u : ZMod ((u ^ (2 * a * k) - 1) / (u ^ a + 1))) =
      if k = 1 then a else 2 * a * k := by
  have hu0 : 0 < u := by omega
  by_cases hk1 : k = 1
  · subst k
    rw [if_pos rfl, quotient_at_one u a hu0]
    exact power_sub_one_order u a hu ha
  · rw [if_neg hk1]
    have hk2 : 2 ≤ k := by omega
    have hr : 0 < 2 * a * k := Nat.mul_pos (Nat.mul_pos (by omega) ha) hk
    have hNdiv : (u ^ (2 * a * k) - 1) / (u ^ a + 1) ∣ u ^ (2 * a * k) - 1 :=
      Nat.div_dvd_of_dvd (denominator_dvd u a k hu0)
    have hreturn : (u : ZMod ((u ^ (2 * a * k) - 1) / (u ^ a + 1))) ^
        (2 * a * k) = 1 :=
      (pow_zmod_eq_one_iff_dvd u _ _ hu0).mpr hNdiv
    refine orderOf_eq_of_pow_and_pow_div_prime hr hreturn ?_
    intro p hp hpr hbad
    have hqpos : 0 < (2 * a * k) / p :=
      Nat.div_pos (Nat.le_of_dvd hr hpr) hp.pos
    have hqhalf : (2 * a * k) / p ≤ a * k := by
      calc
        (2 * a * k) / p ≤ (2 * a * k) / 2 :=
          Nat.div_le_div_left hp.two_le (by omega)
        _ = a * k := by
          rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega)]
    have hupper : u ^ ((2 * a * k) / p) ≤ u ^ (a * k) :=
      Nat.pow_le_pow_right hu0 hqhalf
    have hbound := quotient_half_bound u a k hu ha hk2
    have hone : 1 < u ^ ((2 * a * k) / p) :=
      Nat.one_lt_pow (Nat.ne_of_gt hqpos) (by omega)
    have hpos : 0 < u ^ ((2 * a * k) / p) - 1 := by omega
    have hsmall : u ^ ((2 * a * k) / p) - 1 <
        (u ^ (2 * a * k) - 1) / (u ^ a + 1) := by omega
    have hdiv : (u ^ (2 * a * k) - 1) / (u ^ a + 1) ∣
        u ^ ((2 * a * k) / p) - 1 :=
      (pow_zmod_eq_one_iff_dvd u _ _ hu0).mp hbad
    exact (Nat.not_le_of_lt hsmall) (Nat.le_of_dvd hpos hdiv)

end D5.S3.Arith.Congruence.PowerQuotientOrder
