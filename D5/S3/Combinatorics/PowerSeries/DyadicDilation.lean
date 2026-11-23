/- GID: D5/S3/Combinatorics/PowerSeries/DyadicDilation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PowerSeries/DyadicDilation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Expand]
   utility: none
   digest: Powers of integral series lift to dilated powers modulo every dyadic modulus. -/

import D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.NumberTheory.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! The characteristic-two Frobenius compares squaring with doubling degrees. Divisibility of differences of powers raises the modulus, and iterating gives higher dilations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace D5.S3.Combinatorics.PowerSeries.DyadicDilation

open PowerSeries
open D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators (C_dvd_iff_coeff)

noncomputable def reduce (m : ℕ) : PowerSeries ℤ →+* PowerSeries (ZMod m) :=
  PowerSeries.map (Int.castRingHom (ZMod m))

theorem coeff_reduce_eq_zero (m n : ℕ) (p : PowerSeries ℤ) :
    coeff n (reduce m p) = 0 ↔ (m : ℤ) ∣ coeff n p := by
  rw [reduce, coeff_map]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

private theorem map_mod_eq_iff (m : ℕ) (p q : PowerSeries ℤ) :
    p.map (Int.castRingHom (ZMod m)) = q.map (Int.castRingHom (ZMod m)) ↔
      C (m : ℤ) ∣ p - q := by
  rw [C_dvd_iff_coeff]
  constructor
  · intro h n
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hn := congrArg (coeff n) h
    simp only [coeff_map, map_sub, Int.cast_sub, sub_eq_zero] at hn ⊢
    exact hn
  · intro h
    ext n
    simp only [coeff_map]
    apply sub_eq_zero.mp
    rw [← map_sub, ← map_sub]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h n)

private theorem square_mod_two (p : PowerSeries ℤ) :
    C (2 : ℤ) ∣ p ^ 2 - expand 2 (by decide) p := by
  have h := map_frobenius_expand 2 (by decide) (f := p.map (Int.castRingHom (ZMod 2)))
  rw [ZMod.frobenius_zmod, PowerSeries.map_id] at h
  change expand 2 (by decide) (p.map (Int.castRingHom (ZMod 2))) =
    (p.map (Int.castRingHom (ZMod 2))) ^ 2 at h
  apply (map_mod_eq_iff 2 _ _).mp
  simpa only [map_pow, map_expand] using h.symm

theorem dyadic_lift (p : PowerSeries ℤ) (j : ℕ) :
    C ((2 : ℤ) ^ (j + 1)) ∣
      p ^ (2 ^ (j + 1)) - (expand 2 (by decide) p) ^ (2 ^ j) := by
  have h : (2 : PowerSeries ℤ) ∣ p ^ 2 - expand 2 (by decide) p := by
    simpa only [map_ofNat] using square_mod_two p
  have h' := dvd_sub_pow_of_dvd_sub (p := 2) h j
  simpa only [map_pow, map_ofNat, Nat.cast_ofNat, ← pow_mul, ← pow_succ'] using h'


theorem reduce_lift (p : PowerSeries ℤ) (j r : ℕ) :
    reduce (2^(j+1)) (p ^ (2^(j+1+r))) =
      reduce (2^(j+1)) (expand (2^(r+1)) (by positivity) (p ^ (2^j))) := by
  induction r generalizing p with
  | zero =>
    change reduce (2^(j+1)) (p ^ (2^(j+1))) =
      reduce (2^(j+1)) (expand 2 (by decide) (p ^ (2^j)))
    rw [map_pow (expand 2 (by decide))]
    apply (map_mod_eq_iff _ _ _).2
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using dyadic_lift p j
  | succ r ih =>
    have h := dyadic_lift p (j+1+r)
    have hd : C ((2 : ℤ)^(j+1)) ∣ C ((2 : ℤ)^(j+1+r+1)) :=
      map_dvd C (pow_dvd_pow 2 (by omega))
    have hh := (map_mod_eq_iff (2^(j+1)) _ _).2
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hd.trans h)
    change reduce (2^(j+1)) _ = reduce (2^(j+1)) _ at hh
    rw [show j + 1 + (r + 1) = j+1+r+1 by omega, hh, ih, ← map_pow, ← expand_mul]
    rfl

theorem reduce_lift_mul (p : PowerSeries ℤ) (j r t : ℕ) :
    reduce (2^(j+1)) (p ^ (2^(j+1+r)*t)) =
      expand (2^(r+1)) (by positivity) (reduce (2^(j+1)) p ^ (2^j*t)) := by
  rw [pow_mul, map_pow, reduce_lift, reduce, map_expand, map_pow]
  rw [← map_pow, ← pow_mul]

end D5.S3.Combinatorics.PowerSeries.DyadicDilation
