/- GID: D5/S3/Combinatorics/MinimalForts/LogRotation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/LogRotation
   mirror-E: none(waiver:irrationality-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Basic]
   utility: none
   digest: The logarithmic block parameters give an irrational rotation with uniform real approximation. -/

import D5.S3.Combinatorics.MinimalForts.RotationWindow
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The two logarithmic block increments are multiplicatively independent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.LogRotation

/-- Multiplicative independence of the two actual block increments. -/
theorem ratio_irrational :
    Irrational (Real.log (2 / 3 : ℝ) / Real.log (4 / 3 : ℝ)) := by
  rintro ⟨r, hr⟩
  have ha : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hb : Real.log (2 / 3 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hrneg : (r : ℝ) < 0 := hr ▸ div_neg_of_neg_of_pos hb ha
  have hd : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
  have hnum : (r.num : ℝ) = (r : ℝ) * (r.den : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  have hn : r.num ≤ 0 := by
    have hnreal : (r.num : ℝ) < 0 := by rw [hnum]; exact mul_neg_of_neg_of_pos hrneg hd
    exact_mod_cast hnreal.le
  have hm : (r.num.natAbs : ℝ) = -(r.num : ℝ) := by
    have h : (r.num.natAbs : ℤ) = -r.num := by
      rw [Int.natCast_natAbs, abs_of_nonpos hn]
    have hreal := congrArg (fun z : ℤ => (z : ℝ)) h
    simpa only [Int.cast_natCast, Int.cast_neg] using hreal
  have hrel : (r.den : ℝ) * Real.log (2 / 3 : ℝ) =
      (r.num : ℝ) * Real.log (4 / 3 : ℝ) := by
    rw [hnum, hr]
    field_simp
    <;> ring
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using
      Real.log_pow (2 : ℝ) 2
  have halpha : Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), h4]
  have hbeta : Real.log (2 / 3 : ℝ) = Real.log 2 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  have he : ((r.den : ℝ) + 2 * (r.num.natAbs : ℝ)) * Real.log 2 =
      ((r.den : ℝ) + (r.num.natAbs : ℝ)) * Real.log 3 := by
    rw [halpha, hbeta] at hrel
    rw [hm]
    nlinarith [hrel]
  have hp : (2 : ℝ) ^ (r.den + 2 * r.num.natAbs) =
      (3 : ℝ) ^ (r.den + r.num.natAbs) := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity))
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using he
  have hpNat : (2 : ℕ) ^ (r.den + 2 * r.num.natAbs) =
      (3 : ℕ) ^ (r.den + r.num.natAbs) := by exact_mod_cast hp
  have hexp : r.den + 2 * r.num.natAbs ≠ 0 := by have := r.pos; omega
  have hmod := congrArg (fun n : ℕ => n % 2) hpNat
  norm_num [Nat.pow_mod, Nat.zero_pow (Nat.pos_of_ne_zero hexp)] at hmod


end D5.S3.Combinatorics.MinimalForts.LogRotation
