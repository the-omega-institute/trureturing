/- GID: D5/S3/Arith/GoldenPrimePowerOrder
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenPrimePowerOrder
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: A golden residue at exact prime depth has exact order at every higher precision. -/

import D5.S3.Arith.GoldenApparition
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace D5.S3.Arith.GoldenPrimePowerOrder

open D5.S3.Arith.GoldenApparition

private def pair (q : ℕ) (a b : ℤ) : GoldenMod q := ⟨a, b⟩

/-- The exact order of a golden residue at every prime-power precision. -/
theorem golden_prime_power_order {p m n : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hpm : m + 2 ≤ p * m) (a b : ℤ)
    (hab : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b) :
    orderOf (1 + (p ^ m : GoldenMod (p ^ (n + m))) *
      pair (p ^ (n + m)) a b) = p ^ n := by
  cases n with
  | zero =>
      have hzero : (p ^ m : GoldenMod (p ^ m)) = 0 := by
        simpa only [Nat.cast_pow] using
          (CharP.cast_eq_zero_iff (GoldenMod (p ^ m)) (p ^ m) _).mpr (dvd_refl _)
      rw [zero_add]
      rw [hzero]
      simp
  | succ n =>
      have hdvd : p ∣ p ^ (n + 1 + m) := dvd_pow_self p (by omega)
      let f : ZMod (p ^ (n + 1 + m)) →+* ZMod p := ZMod.castHom hdvd (ZMod p)
      have hred (z : ZMod (p ^ (n + 1 + m)))
          (hz : (p ^ (n + m) : ZMod (p ^ (n + 1 + m))) * z = 0) : f z = 0 := by
        letI : NeZero (p ^ (n + 1 + m)) := ⟨pow_ne_zero _ hp.ne_zero⟩
        have hdiv : p ^ (n + 1 + m) ∣ p ^ (n + m) * z.val := by
          rw [← ZMod.natCast_eq_zero_iff]
          simpa only [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val] using hz
        have hpd : p ∣ z.val := by
          have h : p ^ (n + m) * p ∣ p ^ (n + m) * z.val := by
            simpa only [show n + 1 + m = n + m + 1 by omega, pow_succ] using hdiv
          exact (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos (n + m))).mp h
        simpa only [f, ZMod.castHom_apply, ZMod.cast_eq_val] using
          (ZMod.natCast_eq_zero_iff _ _).mpr hpd
      have hvu : (p : GoldenMod (p ^ (n + 1 + m))) ∣
          (p ^ m : GoldenMod (p ^ (n + 1 + m))) := dvd_pow_self _ (by omega)
      have hpuv :
          (p : GoldenMod (p ^ (n + 1 + m))) * p ^ m * p ∣
            (p ^ m : GoldenMod (p ^ (n + 1 + m))) ^ p := by
        convert (pow_dvd_pow (p : GoldenMod (p ^ (n + 1 + m))) hpm) using 1
        · ring
        · rw [Nat.mul_comm p m, pow_mul]
      have hbin (t : ℕ) :
          ∃ y : GoldenMod (p ^ (n + 1 + m)),
            (1 + (p ^ m : GoldenMod (p ^ (n + 1 + m))) *
              pair (p ^ (n + 1 + m)) a b) ^ (p ^ t) =
              1 + p ^ t * p ^ m * (pair (p ^ (n + 1 + m)) a b + p * y) :=
        ZMod.exists_one_add_mul_pow_prime_pow_eq hp hvu hpuv
          (pair (p ^ (n + 1 + m)) a b) t
      letI : Fact p.Prime := ⟨hp⟩
      apply orderOf_eq_prime_pow
      · obtain ⟨y, hy⟩ := hbin n
        intro hreturn
        rw [hy, ← pow_add] at hreturn
        have hmul :
            (p ^ (n + m) : GoldenMod (p ^ (n + 1 + m))) *
              (pair (p ^ (n + 1 + m)) a b + p * y) = 0 :=
          add_eq_left.mp hreturn
        have ha : (p ^ (n + m) : ZMod (p ^ (n + 1 + m))) *
            (pair (p ^ (n + 1 + m)) a b + p * y).a = 0 := by
          simpa [← Nat.cast_pow, GoldenMod.a_mul, GoldenMod.a_add,
            GoldenMod.a_natCast, GoldenMod.b_natCast, pair] using congrArg GoldenMod.a hmul
        have hb : (p ^ (n + m) : ZMod (p ^ (n + 1 + m))) *
            (pair (p ^ (n + 1 + m)) a b + p * y).b = 0 := by
          simpa [← Nat.cast_pow, GoldenMod.b_mul, GoldenMod.b_add,
            GoldenMod.a_natCast, GoldenMod.b_natCast, pair] using congrArg GoldenMod.b hmul
        have ha0 : (a : ZMod p) = 0 := by
          simpa [f, pair, GoldenMod.a_add, GoldenMod.a_mul] using hred _ ha
        have hb0 : (b : ZMod p) = 0 := by
          simpa [f, pair, GoldenMod.b_add, GoldenMod.b_mul] using hred _ hb
        rcases hab with hna | hnb
        · exact hna ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha0)
        · exact hnb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb0)
      · obtain ⟨y, hy⟩ := hbin (n + 1)
        rw [hy, ← pow_add]
        have hzero : (p ^ (n + 1 + m) : GoldenMod (p ^ (n + 1 + m))) = 0 := by
          simpa only [Nat.cast_pow] using
            (CharP.cast_eq_zero_iff (GoldenMod (p ^ (n + 1 + m)))
              (p ^ (n + 1 + m)) _).mpr (dvd_refl _)
        simp [hzero]

end D5.S3.Arith.GoldenPrimePowerOrder
