/- GID: D5/S1/Recurrence/Sun/GEndpoint
   generality: G
   mirror-B: D5/B/S1/Recurrence/Sun/GEndpoint
   mirror-E: none(waiver:symbolic-endpoint-proof-has-no-separate-evidence-artifact)
   anchors: []
   utility: none
   digest: Factorial scaling and alternating integer parity make Sun's g Turan determinant strict at x=-1. -/

import D5.S1.Recurrence.Sun.Sequences

namespace D5.S1.Recurrence.Sun.GEndpoint

open D5.S1.Recurrence.Sun.Sequences

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The exceptional endpoint in the first clause of Sun's Conjecture 5.2 is strict
at every positive index. -/
theorem g_endpoint_strict (n : ℕ) (hn : 1 ≤ n) :
    g (-1) n ^ 2 > g (-1) (n - 1) * g (-1) (n + 1) := by
  let P : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * g (-1) k
  let Z : ℕ → ℤ := Nat.twoStepInduction 1 0 fun k zk zk1 =>
    -2 * (k + 1) * (k + 2) * zk1 - (k + 1) ^ 4 * zk
  have hPrec (k : ℕ) :
      ((k : ℝ) + 2) ^ 2 * P (k + 2) =
        -2 * ((k : ℝ) + 1) * ((k : ℝ) + 2) * P (k + 1) -
          ((k : ℝ) + 1) ^ 2 * P k := by
    simp [P, g, pow_succ]
    field_simp
  have hscale : ∀ k : ℕ, (Z k : ℝ) = (k.factorial : ℝ) ^ 2 * P k := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => norm_num [Z, Nat.twoStepInduction, P, g]
    | one => norm_num [Z, Nat.twoStepInduction, P, g]
    | more k ih0 ih1 =>
        rw [show Z (k + 2) =
            -2 * (k + 1) * (k + 2) * Z (k + 1) - (k + 1) ^ 4 * Z k by
              simp [Z, Nat.twoStepInduction]]
        push_cast
        rw [ih1, ih0]
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        calc
          _ = (((k : ℝ) + 1) * (k.factorial : ℝ)) ^ 2 *
                (-2 * ((k : ℝ) + 1) * ((k : ℝ) + 2) * P (k + 1) -
                  ((k : ℝ) + 1) ^ 2 * P k) := by ring
          _ = (((k : ℝ) + 1) * (k.factorial : ℝ)) ^ 2 *
                (((k : ℝ) + 2) ^ 2 * P (k + 2)) := by rw [← hPrec k]
          _ = ((((k : ℝ) + 2) *
                (((k : ℝ) + 1) * (k.factorial : ℝ))) ^ 2 * P (k + 2)) := by ring
        ring
  have hparity : ∀ k : ℕ, (Z k : ZMod 2) = if Even k then 1 else 0 := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => norm_num [Z, Nat.twoStepInduction]
    | one => norm_num [Z, Nat.twoStepInduction]
    | more k ih0 ih1 =>
        rw [show Z (k + 2) =
            -2 * (k + 1) * (k + 2) * Z (k + 1) - (k + 1) ^ 4 * Z k by
              simp [Z, Nat.twoStepInduction]]
        push_cast
        have htwo : (2 : ZMod 2) = 0 := by decide
        rw [htwo]
        simp only [neg_zero, zero_mul, zero_sub, ih0]
        rw [ZMod.neg_eq_self_mod_two]
        by_cases hk : Even k
        · have hk1 : Odd (k + 1) := hk.add_one
          have hk2 : Even (k + 2) := by
            obtain ⟨j, rfl⟩ := hk
            exact ⟨j + 1, by omega⟩
          have hkcast : ((k : ℕ) : ZMod 2) = 0 := by
            rw [ZMod.natCast_eq_zero_iff_even]
            exact hk
          rw [if_pos hk, if_pos hk2]
          rw [hkcast]
          norm_num
        · have hkodd : Odd k := Nat.not_even_iff_odd.mp hk
          have hk1 : Even (k + 1) := hkodd.add_one
          have hk2 : ¬ Even (k + 2) := by
            rintro ⟨j, hj⟩
            apply hk
            exact ⟨j - 1, by omega⟩
          rw [if_neg hk, if_neg hk2]
          have hkcast : ((k : ℕ) : ZMod 2) = 1 :=
            ZMod.natCast_eq_one_iff_odd.2 hkodd
          rw [hkcast]
          norm_num
  have hWmod :
      (((n + 1 : ℕ) : ℤ) * Z n + (n : ℤ) ^ 3 * Z (n - 1) : ZMod 2) = 1 := by
    push_cast
    by_cases hne : Even n
    · have hn1o : Odd (n + 1) := hne.add_one
      have hncast : ((n : ℕ) : ZMod 2) = 0 := by
        rw [ZMod.natCast_eq_zero_iff_even]
        exact hne
      rw [hparity n, if_pos hne, hncast]
      norm_num
    · have hno : Odd n := Nat.not_even_iff_odd.mp hne
      have hn1e : Even (n + 1) := hno.add_one
      have hpred : Even (n - 1) := by
        obtain ⟨k, hk⟩ := hno
        obtain rfl : n = 2 * k + 1 := by omega
        exact ⟨k, by omega⟩
      have hncast : ((n : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.2 hno
      rw [hparity (n - 1), if_pos hpred, hncast]
      rw [show (1 : ZMod 2) + 1 = 0 by decide]
      norm_num
  have hWne : ((n + 1 : ℕ) : ℤ) * Z n + (n : ℤ) ^ 3 * Z (n - 1) ≠ 0 := by
    intro hzero
    have hcast := congrArg (fun z : ℤ => (z : ZMod 2)) hzero
    push_cast at hcast
    have hWmod' :
        ((n : ZMod 2) + 1) * (Z n : ZMod 2) +
          (n : ZMod 2) ^ 3 * (Z (n - 1) : ZMod 2) = 1 := by
      simpa using hWmod
    exact one_ne_zero (hWmod'.symm.trans hcast)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let Wk : ℤ := ((k + 2 : ℕ) : ℤ) * Z (k + 1) + ((k + 1 : ℕ) : ℤ) ^ 3 * Z k
  have hcombo_scale :
      ((k + 1).factorial : ℝ) ^ 2 *
          (((k : ℝ) + 2) * P (k + 1) + ((k : ℝ) + 1) * P k) =
        (Wk : ℝ) := by
    dsimp only [Wk]
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul, hscale (k + 1), hscale k]
    push_cast
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hcombo : ((k : ℝ) + 2) * P (k + 1) + ((k : ℝ) + 1) * P k ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hcombo_scale
    have hw :
        (((k + 2 : ℕ) : ℤ) * Z (k + 1) + ((k + 1 : ℕ) : ℤ) ^ 3 * Z k) ≠ 0 := by
      intro hzero
      apply hWne
      have hcast : (((k + 2 : ℕ) : ℤ)) = ((k + 1 : ℕ) : ℤ) + 1 := by
        push_cast
        ring
      rw [hcast] at hzero
      simpa [Nat.succ_eq_add_one] using hzero
    have hWk : Wk ≠ 0 := by
      change ((k + 2 : ℕ) : ℤ) * Z (k + 1) + ((k + 1 : ℕ) : ℤ) ^ 3 * Z k ≠ 0
      exact hw
    have hWkCast : (Wk : ℝ) = ((0 : ℤ) : ℝ) := by
      simpa only [Int.cast_zero] using hcombo_scale.symm
    exact hWk (Int.cast_injective hWkCast)
  have hdet_id :
      ((k : ℝ) + 2) ^ 2 *
          (P (k + 1) ^ 2 - P k * P (k + 2)) =
        (((k : ℝ) + 2) * P (k + 1) + ((k : ℝ) + 1) * P k) ^ 2 := by
    calc
      _ = ((k : ℝ) + 2) ^ 2 * P (k + 1) ^ 2 -
          P k * (((k : ℝ) + 2) ^ 2 * P (k + 2)) := by ring
      _ = ((k : ℝ) + 2) ^ 2 * P (k + 1) ^ 2 -
          P k * (-2 * ((k : ℝ) + 1) * ((k : ℝ) + 2) * P (k + 1) -
            ((k : ℝ) + 1) ^ 2 * P k) := by
            rw [hPrec k]
      _ = _ := by ring
  have hdet : 0 < P (k + 1) ^ 2 - P k * P (k + 2) := by
    have hfac : 0 < ((k : ℝ) + 2) ^ 2 := by positivity
    have hsquare :
        0 < (((k : ℝ) + 2) * P (k + 1) + ((k : ℝ) + 1) * P k) ^ 2 :=
      sq_pos_of_ne_zero hcombo
    nlinarith
  have htranslate :
      P (k + 1) ^ 2 - P k * P (k + 2) =
        g (-1) (k + 1) ^ 2 - g (-1) k * g (-1) (k + 2) := by
    have hsquare (j : ℕ) : ((-1 : ℝ) ^ j) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    have hneighbors : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (k + 2) = 1 := by
      rw [← pow_add]
      rw [show k + (k + 2) = 2 * (k + 1) by omega, pow_mul]
      norm_num
    simp only [P, mul_pow, hsquare, one_mul]
    calc
      _ = g (-1) (k + 1) ^ 2 -
          ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (k + 2)) *
            (g (-1) k * g (-1) (k + 2)) := by ring
      _ = _ := by rw [hneighbors, one_mul]
  rw [htranslate] at hdet
  simpa using hdet

#print axioms g_endpoint_strict

end D5.S1.Recurrence.Sun.GEndpoint
