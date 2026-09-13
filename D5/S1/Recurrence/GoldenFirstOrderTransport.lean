/- GID: D5/S1/Recurrence/GoldenFirstOrderTransport
   generality: G
   mirror-B: none(waiver:new-arithmetic-transport)
   mirror-E: none(waiver:universal-first-order-identity)
   anchors: []
   digest: A quadratic coefficient with square zero has an exact first-order power law; equal powers transport their normalized integer coefficients modulo p. -/

import D5.S3.Arith.GoldenApparition
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S1.Recurrence.GoldenFirstOrderTransport

open D5.S0.Carrier D5.S1.Scale D5.S3.Arith.GoldenApparition

/-- The original golden power, at every natural index including zero. -/
theorem phi_power_b (n : ℕ) : (D5.S0.Carrier.phi ^ n).b = Nat.fib n := by
  cases n with
  | zero => simp
  | succ n => exact golden_phi_pow_b_eq_fib n

theorem phi_power_a_add_b (n : ℕ) :
    (D5.S0.Carrier.phi ^ n).a + (D5.S0.Carrier.phi ^ n).b = Nat.fib (n + 1) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [golden_phi_pow_a_eq_fib, golden_phi_pow_b_eq_fib]
      exact_mod_cast (Nat.fib_add_two (n := n)).symm

/-- No division in ZMod(p^2): cancellation takes place in the integer divisibility witness. -/
theorem cancel_scalar_mod_square (p : ℕ) (hp : 0 < p) (a b : ℤ)
    (h : ((p : ℤ) * a : ZMod (p ^ 2)) = ((p : ℤ) * b : ZMod (p ^ 2))) :
    (a : ZMod p) = (b : ZMod p) := by
  have hd : ((p : ℤ) ^ 2) ∣ (p : ℤ) * (b - a) := by
    have hh := (ZMod.intCast_eq_intCast_iff_dvd_sub ((p : ℤ) * a)
      ((p : ℤ) * b) (p ^ 2)).mp h
    push_cast at hh
    convert hh using 1 <;> ring
  obtain ⟨k, hk⟩ := hd
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  have hba : b - a = (p : ℤ) * k := by
    apply mul_left_cancel₀ hpz
    calc
      _ = (p : ℤ) ^ 2 * k := hk
      _ = _ := by ring
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub a b p).mpr ⟨k, hba⟩

/-- Exact, rather than asymptotic, Taylor formula when the quadratic coefficient squares to zero. -/
theorem golden_power_first_order {q : ℕ} (z : GoldenMod q)
    (hb : z.b * z.b = 0) (k : ℕ) :
    (z ^ k).a = z.a ^ k ∧
      (z ^ k).b = (k : ZMod q) * z.a ^ (k - 1) * z.b := by
  induction k with
  | zero => simp
  | succ k ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [pow_succ]
          simp only [GoldenMod.a_mul, GoldenMod.b_mul, ih.1, ih.2,
            Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
          constructor
          · rw [pow_succ]
            linear_combination ((k : ZMod q) + 1) * z.a ^ k * hb
          · rw [pow_succ]
            linear_combination ((k : ZMod q) + 1) * z.a ^ k * hb

/-- A coefficient divisible by p is square-zero after reduction modulo p^2. -/
lemma reduced_b_square_zero (p : ℕ) (z : GoldenInt) (hz : (p : ℤ) ∣ z.b) :
    (GoldenMod.reduce (p ^ 2) z).b * (GoldenMod.reduce (p ^ 2) z).b = 0 := by
  obtain ⟨k, hk⟩ := hz
  change (z.b : ZMod (p ^ 2)) * (z.b : ZMod (p ^ 2)) = 0
  rw [hk]
  push_cast
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  calc
    _ = (p : ZMod (p ^ 2)) ^ 2 * (k : ZMod (p ^ 2)) ^ 2 := by ring
    _ = 0 := by rw [hp2, zero_mul]

/-- Compare two ways of obtaining exactly the same golden-integer power.
All divisions are witnessed in Z. Neither the equality of indices nor its quotient consequence
is assumed: callers establish x^k=y^l using the actual exponent arithmetic. -/
theorem coefficient_transport (p : ℕ) (hp : 0 < p)
    (x y : GoldenInt) (k l : ℕ) (a b : ℤ)
    (hx : x.b = (p : ℤ) * a) (hy : y.b = (p : ℤ) * b)
    (hpow : x ^ k = y ^ l) :
    (k : ZMod p) * (x.a : ZMod p) ^ (k - 1) * (a : ZMod p) =
      (l : ZMod p) * (y.a : ZMod p) ^ (l - 1) * (b : ZMod p) := by
  have he := congrArg (fun z : GoldenInt => (GoldenMod.reduce (p ^ 2) z).b) hpow
  simp only [map_pow] at he
  rw [(golden_power_first_order _ (reduced_b_square_zero p x ⟨a, hx⟩) k).2,
      (golden_power_first_order _ (reduced_b_square_zero p y ⟨b, hy⟩) l).2] at he
  change (k : ZMod (p ^ 2)) * (x.a : ZMod (p ^ 2)) ^ (k - 1) * (x.b : ZMod (p ^ 2)) =
      (l : ZMod (p ^ 2)) * (y.a : ZMod (p ^ 2)) ^ (l - 1) * (y.b : ZMod (p ^ 2)) at he
  rw [hx, hy] at he
  have hphe : (((p : ℤ) * ((k : ℤ) * x.a ^ (k - 1) * a) : ℤ) : ZMod (p ^ 2)) =
      (((p : ℤ) * ((l : ℤ) * y.a ^ (l - 1) * b) : ℤ) : ZMod (p ^ 2)) := by
    push_cast
    linear_combination he
  have hh := cancel_scalar_mod_square p hp
    ((k : ℤ) * x.a ^ (k - 1) * a) ((l : ℤ) * y.a ^ (l - 1) * b) hphe
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using hh

end D5.S1.Recurrence.GoldenFirstOrderTransport
