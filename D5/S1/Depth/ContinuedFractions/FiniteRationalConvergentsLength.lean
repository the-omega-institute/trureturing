/- GID: D5/S1/Depth/ContinuedFractions/FiniteRationalConvergentsLength
   generality: G
   mirror-B: D5/B/S1/Depth/ContinuedFractions/FiniteRationalConvergentsLength
   mirror-E: none(waiver:general-rational-length-estimate)
   anchors: [mathlib/module/Mathlib.Data.Nat.Log]
   utility: none
   digest: Rational Euclidean lists have logarithmic length in their reduced denominator. -/

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license; the complete license is retained in
Library/HilbertOperators/aicyberg2026shor.md. Authors: aicyberg.
Source: solanaqubits/leanbook, commit 9b742770a2a5dbcf30cf9abc44e711194e957a00,
Verification/QuantumShorContinuedFractions.lean, second_den_sum_le and
convergents_length_log. The receiving imports and module grouping are adapted.
Retire this slice when equivalent declarations exist in the receiving pinned
Mathlib, replacing the slice with direct imports at that repository pin.
-/

import D5.S1.Depth.ContinuedFractions.FiniteRationalConvergents
import Mathlib.Data.Nat.Log

namespace QuantumShorContinuedFractions

private theorem second_den_sum_le (x : ℚ) (h : Int.fract x ≠ 0)
    (h' : Int.fract (Int.fract x)⁻¹ ≠ 0) :
    ((Int.fract (Int.fract x)⁻¹)⁻¹).den + ((Int.fract x)⁻¹).den ≤ x.den := by
  let t := Int.fract x
  let u := t⁻¹
  have ht : 0 < t := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm h)
  have hn : 0 < t.num := Rat.num_pos.mpr ht
  have hu : 1 ≤ u := by
    dsimp [u]; exact (one_le_inv₀ ht).mpr (Int.fract_lt_one x).le
  have hf : (1 : ℤ) ≤ ⌊u⌋ := by exact Int.le_floor.mpr hu
  have hnum : u.num = x.den := by
    dsimp [u, t]
    rw [Rat.num_inv, Int.sign_eq_one_of_pos hn, one_mul, Rat.den_intFract]
  have hden : (Int.fract u).den = u.den := Rat.den_intFract _
  have hnon : 0 ≤ (Int.fract u).num := Rat.num_nonneg.mpr (Int.fract_nonneg u)
  have heq : (Int.fract u).num + ⌊u⌋ * u.den = u.num := by
    have hv := Int.fract_add_floor u
    have hm := congrArg (fun z : ℚ => z * u.den) hv
    have mulden (z : ℚ) : z * (z.den : ℚ) = z.num :=
      (eq_div_iff (by exact_mod_cast z.den_ne_zero)).mp z.num_div_den.symm
    rw [add_mul, ← hden, mulden (Int.fract u), hden, mulden u] at hm
    exact_mod_cast hm
  have hle : (Int.fract u).num + (u.den : ℤ) ≤ (x.den : ℤ) := by
    rw [hnum] at heq
    have hp : (0 : ℤ) ≤ u.den := by positivity
    nlinarith
  change ((Int.fract u)⁻¹).den + u.den ≤ x.den
  rw [Rat.den_inv_of_ne_zero h']
  exact_mod_cast (show ((Int.fract u).num.natAbs : ℤ) + (u.den : ℤ) ≤ (x.den : ℤ) by
    simpa [Int.natCast_natAbs, abs_of_nonneg hnon] using hle)

/-- At most 2 floor(log₂ denominator)+1 Euclidean stages. This counts complete
quotients, not bit operations or all list-map operations. -/
theorem convergents_length_log (x : ℚ) :
    (convergents x).length ≤ 2 * Nat.log 2 x.den + 1 := by
  induction hd : x.den using Nat.strong_induction_on generalizing x with
  | h d ih =>
    by_cases h : Int.fract x = 0
    · rw [convergents, dif_pos h]; simp
    · let t := (Int.fract x)⁻¹
      have ht : t.den < d := by simpa [t, hd] using tail_den_lt x h
      by_cases h' : Int.fract t = 0
      · have hd2 : 2 ≤ d := lt_of_le_of_lt t.pos ht
        have hl : 1 ≤ Nat.log 2 d := Nat.le_log_of_pow_le (by decide) (by simpa using hd2)
        rw [convergents, dif_neg h, List.length_cons, List.length_map]
        change (convergents t).length + 1 ≤ _
        rw [convergents, dif_pos h', List.length_singleton]
        omega
      · let u := (Int.fract t)⁻¹
        have hu : u.den < t.den := tail_den_lt t h'
        have hsum : u.den + t.den ≤ d := by
          simpa [u, t, hd] using second_den_sum_le x h h'
        have hdouble : u.den * 2 ≤ d := by omega
        have hl : Nat.log 2 u.den + 1 ≤ Nat.log 2 d := by
          have hm := Nat.log_mono_right (b := 2) hdouble
          rwa [Nat.log_mul_base (by decide) u.den_ne_zero] at hm
        have hu' := ih u.den (hu.trans ht) u rfl
        rw [convergents, dif_neg h, List.length_cons, List.length_map]
        change (convergents t).length + 1 ≤ _
        rw [convergents, dif_neg h', List.length_cons, List.length_map]
        change (convergents u).length + 1 + 1 ≤ _
        omega

end QuantumShorContinuedFractions
