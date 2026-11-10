/- GID: D5/S3/Arith/Congruence/PowerPlusOneDivisibility
   generality: G
   mirror-B: none(waiver:consumed-symbolic-support)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Exponent congruence characterizes divisibility by a power plus one over every base at least two. -/
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Lean.Elab.Tactic.Omega

/-! Exact exponent congruence for divisibility of powers plus one.

For every natural base at least two and every positive first exponent, the
divisibility condition is equivalent to a residue condition on the other exponent.
The physical two-bit classification consumes this arithmetic equivalence. -/

namespace PowerPlusOneDivisibility

private theorem nat_modEq_neg_one_iff_dvd_add_one (d x : ℕ) :
    Int.ModEq (d : ℤ) (x : ℤ) (-1) ↔ d ∣ x + 1 := by
  rw [Int.modEq_iff_dvd]
  rw [show (-1 : ℤ) - (x : ℤ) = -((x : ℤ) + 1) by omega, Int.dvd_neg]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (Int.natCast_dvd_natCast (m := d) (n := x + 1))

/-- Exact exponents for divisibility by a power plus one, for every natural
base at least two. The exponent `m` is unrestricted, including zero. -/
theorem dvd_pow_add_one_iff_mod_two_mul (u a m : ℕ) (hu : 2 ≤ u) (ha : 0 < a) :
    (u ^ a + 1) ∣ (u ^ m + 1) ↔ m % (2 * a) = a := by
  let N : ℕ := u ^ a + 1
  let r : ℕ := m % (2 * a)
  have hN : N = u ^ a + 1 := rfl
  have hu1 : 1 < u := by omega
  have hua : 0 < u ^ a := Nat.pow_pos (by omega : 0 < u)
  have hrlt : r < 2 * a := Nat.mod_lt m (by omega)
  have hhalf : Int.ModEq (N : ℤ) ((u : ℤ) ^ a) (-1) := by
    simpa only [Nat.cast_pow] using
      (nat_modEq_neg_one_iff_dvd_add_one N (u ^ a)).mpr
        (show N ∣ u ^ a + 1 from dvd_refl N)
  have hperiod : Int.ModEq (N : ℤ) ((u : ℤ) ^ (2 * a)) 1 := by
    rw [mul_comm 2 a, pow_mul]
    simpa using hhalf.pow 2
  have hred : Int.ModEq (N : ℤ) ((u : ℤ) ^ m) ((u : ℤ) ^ r) := by
    calc
      (u : ℤ) ^ m = (u : ℤ) ^ r *
          ((u : ℤ) ^ (2 * a)) ^ (m / (2 * a)) := by
        dsimp [r]
        rw [← pow_mul, ← pow_add, Nat.mod_add_div]
      _ ≡ (u : ℤ) ^ r * 1 ^ (m / (2 * a)) [ZMOD (N : ℤ)] :=
        Int.ModEq.rfl.mul (hperiod.pow (m / (2 * a)))
      _ = (u : ℤ) ^ r := by simp
  constructor
  · intro hm
    have hmz : Int.ModEq (N : ℤ) ((u : ℤ) ^ m) (-1) := by
      simpa only [Nat.cast_pow] using
        (nat_modEq_neg_one_iff_dvd_add_one N (u ^ m)).mpr hm
    have hmr : Int.ModEq (N : ℤ) ((u : ℤ) ^ r) (-1) := hred.symm.trans hmz
    have hr : N ∣ u ^ r + 1 :=
      (nat_modEq_neg_one_iff_dvd_add_one N (u ^ r)).mp
        (by simpa only [Nat.cast_pow] using hmr)
    by_cases hra : r < a
    · have hp : u ^ r < u ^ a := Nat.pow_lt_pow_right hu1 hra
      have hle : N ≤ u ^ r + 1 := Nat.le_of_dvd (by omega) hr
      omega
    · let t : ℕ := r - a
      have hsplit : r = a + t := by dsimp [t]; omega
      have ht : t < a := by dsimp [t]; omega
      have hhigh : Int.ModEq (N : ℤ) ((u : ℤ) ^ r) (-((u : ℤ) ^ t)) := by
        rw [hsplit, pow_add]
        simpa only [neg_one_mul] using hhalf.mul_right ((u : ℤ) ^ t)
      have htint : Int.ModEq (N : ℤ) ((u : ℤ) ^ t) 1 := by
        simpa only [neg_neg] using (hhigh.symm.trans hmr).neg
      have htnat : Nat.ModEq N (u ^ t) 1 := by
        apply Int.natCast_modEq_iff.mp
        simpa only [Nat.cast_pow, Nat.cast_one] using htint
      have htpow : u ^ t < u ^ a := Nat.pow_lt_pow_right hu1 ht
      have heq : u ^ t = 1 := htnat.eq_of_lt_of_lt (by omega) (by omega)
      have htzero : t = 0 := by
        by_contra htzero
        have htpos : 0 < t := Nat.pos_of_ne_zero htzero
        have hone : 1 < u ^ t := by
          simpa only [pow_zero] using
            (Nat.pow_lt_pow_right hu1 htpos : u ^ 0 < u ^ t)
        omega
      change r = a
      omega
  · intro hm
    have hra : r = a := hm
    have hmz : Int.ModEq (N : ℤ) ((u : ℤ) ^ m) (-1) :=
      hred.trans (by simpa only [hra] using hhalf)
    exact (nat_modEq_neg_one_iff_dvd_add_one N (u ^ m)).mp
      (by simpa only [Nat.cast_pow] using hmz)

end PowerPlusOneDivisibility
