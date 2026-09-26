/- GID: D5/S3/Arith/GoldenPrimePeriodBounds
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenPrimePeriodBounds
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Golden Frobenius bounds the Fibonacci matrix period at every prime above five. -/

import D5.S3.Arith.GoldenMatrixPeriodBridge
import Mathlib.Data.Int.Fib.Basic

namespace D5.S3.Arith.GoldenPrimePeriodBounds

open scoped Matrix
open D5.S0.Carrier D5.S1.Scale
open D5.S3.Arith.GoldenApparition D5.S3.Arith.GoldenMatrixPeriodBridge

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The split and inert Frobenius bounds for the period of the actual
Fibonacci matrix modulo a prime. -/
theorem golden_prime_period_bounds {p : ℕ} (hp : p.Prime) (hpFive : 5 < p) :
    (legendreSym 5 p = 1 →
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ∣ p - 1 ∧
      ¬ p ∣ orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))) ∧
    (legendreSym 5 p = -1 →
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ∣ 2 * (p + 1) ∧
      ¬ p ∣ orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))) := by
  have hpNotDvdFive : ¬ p ∣ 5 := by
    intro h
    have hle := Nat.le_of_dvd (by decide : 0 < 5) h
    omega
  have hentry := fibonacci_apparition_entry_point hp hpNotDvdFive
  have hfp : ((Nat.fib p : ℕ) : ZMod p) = (legendreSym 5 p : ZMod p) := by
    simpa only [Int.fib_natCast, Int.cast_natCast] using hentry.2
  have hpair (n : ℕ) :
      (GoldenMod.phi : GoldenMod p) ^ (n + 1) =
        ⟨(Nat.fib n : ZMod p), (Nat.fib (n + 1) : ZMod p)⟩ := by
    have h := congrArg (GoldenMod.reduce p) (golden_phi_pow_eq_fib_pair n)
    have hr : GoldenMod.reduce p
        (⟨(Nat.fib n : ℤ), (Nat.fib (n + 1) : ℤ)⟩ : GoldenInt) =
        ⟨(Nat.fib n : ZMod p), (Nat.fib (n + 1) : ZMod p)⟩ := by
      apply GoldenMod.ext
      · change (((Nat.fib n : ℕ) : ℤ) : ZMod p) = (Nat.fib n : ZMod p)
        rw [Int.cast_natCast]
      · change (((Nat.fib (n + 1) : ℕ) : ℤ) : ZMod p) =
          (Nat.fib (n + 1) : ZMod p)
        rw [Int.cast_natCast]
    have hphi : GoldenMod.reduce p D5.S0.Carrier.phi = GoldenMod.phi := by
      apply GoldenMod.ext <;>
        norm_num [GoldenMod.reduce, D5.S0.Carrier.phi, GoldenMod.phi]
    simpa only [map_pow, hphi, hr] using h
  have horder := (golden_matrix_faithful p).2.2
  constructor
  · intro heps
    have hfprev : ((Nat.fib (p - 1) : ℕ) : ZMod p) = 0 := by
      have h := hentry.1
      rw [heps] at h
      have hindex : (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) := by omega
      rw [hindex, Int.fib_natCast, Int.cast_natCast] at h
      exact h
    have hfcurrent : ((Nat.fib p : ℕ) : ZMod p) = 1 := by
      simpa [heps] using hfp
    have hpow : (GoldenMod.phi : GoldenMod p) ^ p = GoldenMod.phi := by
      have h := hpair (p - 1)
      have hindex : p - 1 + 1 = p := by omega
      rw [hindex] at h
      apply GoldenMod.ext
      · simpa [GoldenMod.phi] using (congrArg GoldenMod.a h).trans hfprev
      · simpa [GoldenMod.phi] using (congrArg GoldenMod.b h).trans hfcurrent
    have hinv : (GoldenMod.phi : GoldenMod p) * (GoldenMod.phi - 1) = 1 := by
      apply GoldenMod.ext <;>
        simp [GoldenMod.phi, sub_eq_add_neg]
    have hreturn : (GoldenMod.phi : GoldenMod p) ^ (p - 1) = 1 := by
      have hindex : p - 1 + 1 = p := by omega
      calc
        (GoldenMod.phi : GoldenMod p) ^ (p - 1) =
            (GoldenMod.phi : GoldenMod p) ^ (p - 1) *
              (GoldenMod.phi * (GoldenMod.phi - 1)) := by rw [hinv, mul_one]
        _ = (GoldenMod.phi : GoldenMod p) ^ p * (GoldenMod.phi - 1) := by
          rw [← mul_assoc, ← pow_succ, hindex]
        _ = 1 := by rw [hpow, hinv]
    have hperiod :
        orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ∣ p - 1 := by
      rw [← horder]
      exact orderOf_dvd_of_pow_eq_one hreturn
    refine ⟨hperiod, ?_⟩
    intro hpdvd
    have hbad : p ∣ p - 1 := dvd_trans hpdvd hperiod
    have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hbad
    omega
  · intro heps
    have hfnext : ((Nat.fib (p + 1) : ℕ) : ZMod p) = 0 := by
      have h := hentry.1
      rw [heps] at h
      have hindex : (p : ℤ) - -1 = ((p + 1 : ℕ) : ℤ) := by omega
      rw [hindex, Int.fib_natCast, Int.cast_natCast] at h
      exact h
    have hfcurrent : ((Nat.fib p : ℕ) : ZMod p) = -1 := by
      simpa [heps] using hfp
    have hpow : (GoldenMod.phi : GoldenMod p) ^ (p + 1) = -1 := by
      have h := hpair p
      apply GoldenMod.ext
      · simpa using (congrArg GoldenMod.a h).trans hfcurrent
      · simpa using (congrArg GoldenMod.b h).trans hfnext
    have hreturn : (GoldenMod.phi : GoldenMod p) ^ (2 * (p + 1)) = 1 := by
      calc
        (GoldenMod.phi : GoldenMod p) ^ (2 * (p + 1)) =
            ((GoldenMod.phi : GoldenMod p) ^ (p + 1)) ^ 2 := by
              rw [Nat.mul_comm 2 (p + 1), pow_mul]
        _ = 1 := by rw [hpow]; norm_num
    have hperiod :
        orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ∣
          2 * (p + 1) := by
      rw [← horder]
      exact orderOf_dvd_of_pow_eq_one hreturn
    refine ⟨hperiod, ?_⟩
    intro hpdvd
    have hbad : p ∣ 2 * (p + 1) := dvd_trans hpdvd hperiod
    rcases hp.dvd_mul.mp hbad with htwo | hnext
    · have hle := Nat.le_of_dvd (by decide : 0 < 2) htwo
      omega
    · have hone : p ∣ 1 := (Nat.dvd_add_self_left).mp hnext
      have hle := Nat.le_of_dvd (by decide : 0 < 1) hone
      omega

end D5.S3.Arith.GoldenPrimePeriodBounds
