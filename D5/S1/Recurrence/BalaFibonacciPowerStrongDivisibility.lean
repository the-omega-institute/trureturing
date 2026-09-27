/- GID: D5/S1/Recurrence/BalaFibonacciPowerStrongDivisibility
   generality: G
   mirror-B: D5/B/S1/Recurrence/BalaFibonacciPowerStrongDivisibility
   mirror-E: none(waiver:formal-unit-only)
   anchors: []
   utility: none
   digest: Fibonacci minus one at powers of every odd base is strongly divisible. -/

import D5.S1.Recurrence.LucasCompanion
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Image
import Mathlib.Dynamics.PeriodicPts.Defs

set_option autoImplicit false

/-!
The source sequence is `a(t) = F_t - 1`. For an odd index, the Fibonacci
companion power has determinant minus one. If its off-diagonal entry is
one modulo a prime power, its diagonal entries are `x + 1` and `x`, with
`x * (x + 1) = 0`. Consecutive integers are coprime, so the entire prime
power divides one factor. This gives exactly the companion or its inverse.

The inverse pair is a point of a set dynamical system under taking kth
powers. Its return times are closed under gcd and divisibility by the
existing periodic-point theorems. Prime-power divisibility then recovers
the natural gcd equality, including zero sequence values when `k = 1`.
No division by two or five is used. All adapters remain inside `result`.
-/

namespace D5.S1.Recurrence.BalaFibonacciPowerStrongDivisibility

open Matrix LucasEvenDescent LucasCompanion

/-- Bala's A000071 conjecture, with every positive odd base and positive indices. -/
theorem result (k n m : ℕ) (hk : Odd k) (hn : 0 < n) (hm : 0 < m) :
    Nat.gcd (Nat.fib (k ^ n) - 1) (Nat.fib (k ^ m) - 1) =
      Nat.fib (k ^ Nat.gcd n m) - 1 := by
  have hfib (q j : ℕ) : lucasU (1 : ZMod q) (-1) (j : ℤ) = (Nat.fib j : ZMod q) := by
    induction j using Nat.twoStepInduction with
    | zero => simpa using (lucas_recurrence (1 : ZMod q) (-1)).1
    | one => simpa using (lucas_recurrence (1 : ZMod q) (-1)).2.1
    | more j h0 h1 =>
      have h1' : lucasU (1 : ZMod q) (-1) ((j : ℤ) + 1) =
          (Nat.fib (j + 1) : ZMod q) := by
        simpa only [Nat.cast_add, Nat.cast_one] using h1
      have h := (lucas_recurrence (1 : ZMod q) (-1)).2.2 (j : ℤ)
      simpa [Nat.cast_add, Nat.fib_add_two, h0, h1', sub_eq_add_neg, add_comm] using h
  have hreturn (p e : ℕ) (hp : Nat.Prime p) (he : 0 < e) (t : ℕ) (ht : Odd t) :
      (Nat.fib t : ZMod (p ^ e)) = 1 ↔
        companion (1 : ZMod (p ^ e)) (-1) ^ t = companion 1 (-1) ∨
        companion (1 : ZMod (p ^ e)) (-1) ^ t = (companion 1 (-1))⁻¹ := by
    let : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
    let Q := companion (1 : ZMod (p ^ e)) (-1)
    have hs := companion_power_shape (1 : ZMod (p ^ e)) (-1) (t : ℤ)
    change (↑(Q ^ (t : ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ e))) = _ at hs
    have hs' : (↑(Q ^ t) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ e))) =
        !![(Nat.fib (t + 1) : ZMod (p ^ e)), Nat.fib t;
           Nat.fib t, Nat.fib (t + 1) - Nat.fib t] := by
      rw [show (t : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) by simp] at hs
      simpa only [Q, zpow_natCast, hfib,
        Units.val_neg, Units.val_one, neg_neg, one_mul] using hs
    constructor
    · intro hf
      let x : ZMod (p ^ e) := Nat.fib (t + 1) - 1
      have hshape : (↑(Q ^ t) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ e))) =
          !![x + 1, 1; 1, x] := by
        rw [hs', hf]
        simp [x]
      have hd := companion_power_det (1 : ZMod (p ^ e)) (-1) (t : ℤ)
      have hd' : (↑(Q ^ t) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ e))).det = -1 := by
        simpa only [Q, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_neg,
          Units.val_one, ht.neg_one_pow] using hd
      rw [hshape, Matrix.det_fin_two] at hd'
      have hx : x * (x + 1) = 0 := by
        simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, one_mul] at hd'
        linear_combination hd'
      have hdiv : p ^ e ∣ x.val * (x.val + 1) := by
        apply (ZMod.natCast_eq_zero_iff _ _).mp
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using hx
      have hxsplit : x = 0 ∨ x = -1 := by
        by_cases ha : p ∣ x.val
        · have hb : ¬p ∣ x.val + 1 := by
            intro hb
            exact hp.not_dvd_one ((Nat.dvd_add_iff_right ha).mpr hb)
          have hd0 : p ^ e ∣ x.val :=
            (hp.coprime_pow_of_not_dvd hb).symm.dvd_mul_right.mp hdiv
          left
          simpa only [ZMod.natCast_zmod_val] using
            (ZMod.natCast_eq_zero_iff x.val (p ^ e)).mpr hd0
        · have hd1 : p ^ e ∣ x.val + 1 :=
            (hp.coprime_pow_of_not_dvd ha).symm.dvd_mul_left.mp hdiv
          right
          have hz := (ZMod.natCast_eq_zero_iff (x.val + 1) (p ^ e)).mpr hd1
          have : x + 1 = 0 := by simpa using hz
          exact eq_neg_of_add_eq_zero_left this
      change Q ^ t = Q ∨ Q ^ t = Q⁻¹
      rcases hxsplit with hx0 | hx1
      · left
        apply Units.ext
        rw [hshape, hx0]
        simp [Q, companion]
      · right
        apply Units.ext
        rw [hshape, hx1]
        simp [Q, companion]
    · intro h
      change Q ^ t = Q ∨ Q ^ t = Q⁻¹ at h
      rcases h with h | h
      · have hh := congrArg (fun g : (Matrix (Fin 2) (Fin 2) (ZMod (p ^ e)))ˣ =>
          (g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ e))) 1 0) h
        change (↑(Q ^ t) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ e))) 1 0 = _ at hh
        rw [hs'] at hh
        simpa [Q, companion] using hh
      · have hh := congrArg (fun g : (Matrix (Fin 2) (Fin 2) (ZMod (p ^ e)))ˣ =>
          (g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ e))) 1 0) h
        change (↑(Q ^ t) : Matrix (Fin 2) (Fin 2) (ZMod (p ^ e))) 1 0 = _ at hh
        rw [hs'] at hh
        simpa [Q, companion] using hh
  have hperiod (p e : ℕ) (hp : Nat.Prime p) (he : 0 < e) (r : ℕ) :
      p ^ e ∣ Nat.fib (k ^ r) - 1 ↔
        Function.IsPeriodicPt
          (Set.image (fun g : (Matrix (Fin 2) (Fin 2) (ZMod (p ^ e)))ˣ => g ^ k))
          r {companion 1 (-1), (companion 1 (-1))⁻¹} := by
    let Q := companion (1 : ZMod (p ^ e)) (-1)
    have hkpos : 0 < k := hk.pos
    have hfpos : 1 ≤ Nat.fib (k ^ r) := Nat.fib_pos.mpr (pow_pos hkpos _)
    rw [← ZMod.natCast_eq_zero_iff (Nat.fib (k ^ r) - 1) (p ^ e),
      Nat.cast_sub hfpos, Nat.cast_one, sub_eq_zero, hreturn p e hp he _ hk.pow]
    change Q ^ (k ^ r) = Q ∨ Q ^ (k ^ r) = Q⁻¹ ↔
      (Set.image (fun g => g ^ k))^[r] {Q, Q⁻¹} = {Q, Q⁻¹}
    rw [← Set.image_iterate_eq, pow_iterate, Set.image_pair, inv_pow]
    constructor
    · rintro (h | h)
      · rw [h]
      · rw [h, inv_inv, Set.pair_comm]
    · intro h
      have hh : Q ^ (k ^ r) ∈ ({Q, Q⁻¹} : Set _) := by
        rw [← h]
        exact Set.mem_insert _ _
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hh
  apply Nat.dvd_antisymm
  · apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro p e hp hd
    by_cases he : e = 0
    · simp [he]
    · exact (hperiod p e hp (Nat.pos_of_ne_zero he) _).mpr
        (((hperiod p e hp (Nat.pos_of_ne_zero he) n).mp
          (hd.trans (Nat.gcd_dvd_left _ _))).gcd
        ((hperiod p e hp (Nat.pos_of_ne_zero he) m).mp
          (hd.trans (Nat.gcd_dvd_right _ _))))
  · apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro p e hp hd
    by_cases he : e = 0
    · simp [he]
    · have h := (hperiod p e hp (Nat.pos_of_ne_zero he) _).mp hd
      exact Nat.dvd_gcd
        ((hperiod p e hp (Nat.pos_of_ne_zero he) n).mpr
          (h.trans_dvd (Nat.gcd_dvd_left _ _)))
        ((hperiod p e hp (Nat.pos_of_ne_zero he) m).mpr
          (h.trans_dvd (Nat.gcd_dvd_right _ _)))

#print axioms result

end D5.S1.Recurrence.BalaFibonacciPowerStrongDivisibility
