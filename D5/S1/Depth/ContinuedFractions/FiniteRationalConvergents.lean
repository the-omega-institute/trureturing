/- GID: D5/S1/Depth/ContinuedFractions/FiniteRationalConvergents
   generality: G
   mirror-B: D5/B/S1/Depth/ContinuedFractions/FiniteRationalConvergents
   mirror-E: none(waiver:general-rational-recursion-proof)
   anchors: [mathlib/module/Mathlib.NumberTheory.DiophantineApproximation.Basic]
   utility: none
   digest: Finite rational Euclidean lists coincide with all real convergents. -/

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license; the complete license is retained in
Library/HilbertOperators/aicyberg2026shor.md. Authors: aicyberg.
Source: solanaqubits/leanbook, commit 9b742770a2a5dbcf30cf9abc44e711194e957a00,
Verification/QuantumShorContinuedFractions.lean.
The receiving module grouping and tail_den_lt visibility are adapted.
Retire this slice when equivalent declarations exist in the receiving pinned
Mathlib, replacing the slice with direct imports at that repository pin.
-/

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Rat.Floor

namespace QuantumShorContinuedFractions

theorem tail_den_lt (x : ℚ) (h : Int.fract x ≠ 0) :
    ((Int.fract x)⁻¹).den < x.den := by
  rw [Rat.den_inv_of_ne_zero h, ← Rat.den_intFract x]
  have hn : 0 ≤ (Int.fract x).num := Rat.num_nonneg.mpr (Int.fract_nonneg x)
  have hl := Int.fract_lt_one x
  rw [← Rat.num_div_den (Int.fract x), div_lt_one (by positivity)] at hl
  have hi : (Int.fract x).num < ((Int.fract x).den : ℤ) := by exact_mod_cast hl
  exact_mod_cast (show ((Int.fract x).num.natAbs : ℤ) < ((Int.fract x).den : ℤ) by
    simpa [Int.natCast_natAbs, abs_of_nonneg hn] using hi)

/-- Euclidean continued fractions: floor is integer division, and the reciprocal
fractional part is the next complete quotient. Stops at an integer. -/
def convergents (x : ℚ) : List ℚ :=
  if h : Int.fract x = 0 then [⌊x⌋]
  else (⌊x⌋ : ℚ) :: (convergents (Int.fract x)⁻¹).map (fun z => (⌊x⌋ : ℚ) + z⁻¹)
termination_by x.den
decreasing_by exact tail_den_lt x h

/-- Every real convergent of a rational input is in the finite executable list,
including the repeated terminal convergents of Mathlib's totalized definition. -/
private theorem real_convergent_mem (x : ℚ) (k : ℕ) :
    Real.convergent (x : ℝ) k ∈ convergents x := by
  induction x using convergents.induct generalizing k with
  | case1 x h =>
    have hx : x = (⌊x⌋ : ℚ) := by
      have := Int.fract_add_floor x
      rw [h, zero_add] at this
      exact this.symm
    rw [convergents, dif_pos h]
    have hc : (x : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast hx
    simp [hc]
  | case2 x h ih =>
    rw [convergents, dif_neg h]
    cases k with
    | zero => simp
    | succ k =>
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      refine ⟨Real.convergent (((Int.fract x)⁻¹ : ℚ) : ℝ) k, ih k, ?_⟩
      simp

/-- The executable list has no entries other than actual convergents. -/
theorem mem_convergents_iff (x z : ℚ) :
    z ∈ convergents x ↔ ∃ k, Real.convergent (x : ℝ) k = z := by
  constructor
  · induction x using convergents.induct generalizing z with
    | case1 x h =>
      rw [convergents, dif_pos h, List.mem_singleton]
      intro hz
      exact ⟨0, by simp [hz]⟩
    | case2 x h ih =>
      rw [convergents, dif_neg h]
      intro hz
      rcases List.mem_cons.mp hz with hz | hz
      · exact ⟨0, by simp [hz]⟩
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
        obtain ⟨k, hk⟩ := ih u hu
        refine ⟨k + 1, ?_⟩
        simpa using congrArg (fun z : ℚ => (⌊x⌋ : ℚ) + z⁻¹) hk
  · rintro ⟨k, rfl⟩; exact real_convergent_mem x k

/-- Observable inputs only: measured integer, register size, modulus bound. -/
def candidates (y Q N : ℕ) : List ℚ :=
  (convergents ((y : ℚ) / Q)).filter (fun z => z.den < N)

/-- Reduction uses the canonical numerator and positive denominator of a rational. -/
def reduced (s r : ℕ) : ℚ := (s : ℚ) / r

theorem reduced_den (s r : ℕ) (hr : 0 < r) :
    (reduced s r).den = r / Nat.gcd s r := by
  simp [reduced, Rat.natCast_div_eq_divInt, Rat.den_mkRat, hr.ne', Nat.gcd_comm]


end QuantumShorContinuedFractions
