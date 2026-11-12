/- GID: D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Beatty/IteratedBeattyRangeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.NumberTheory.Rayleigh, mathlib/module/Mathlib.NumberTheory.Real.Irrational]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.claim; result=D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.result; claim=D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.claim
   digest: The positive fixed point two at modulus sqrt two refutes the universal iterated Beatty extension. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#29668; Question 1).
Direct frozen dependencies: none (pinned Mathlib only).
The designated literal refutation result is exempt from four-slot escape
registration under CLAUDE.md section 3.9. No other theorem is declared here.
-/

import Mathlib.NumberTheory.Rayleigh
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

namespace D5.S3.Arith.Beatty.IteratedBeattyRangeRefutation

/-- The range of the actual `n`-fold floor-map composition, with a positive
natural preimage. Mathlib's `beattySeq α k` is `⌊(k : ℝ) * α⌋`. -/
def nativeRange (α : ℝ) (n x : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ (beattySeq α)^[n] (k : ℤ) = (x : ℤ)

/-- All strict fractional-part conditions of the source characterization. -/
def fractionalTest (α : ℝ) (n x : ℕ) : Prop :=
  (1 - 1 / α < Int.fract ((x : ℝ) / α) ∧ Int.fract ((x : ℝ) / α) < 1) ∧
    ∀ i : ℕ, 2 ≤ i → i ≤ n →
      1 - 2 / α < Int.fract ((x : ℝ) / α ^ i) -
        Int.fract ((x : ℝ) / α ^ (i - 1)) / α ∧
      Int.fract ((x : ℝ) / α ^ i) -
        Int.fract ((x : ℝ) / α ^ (i - 1)) / α < 1 - 1 / α

/-- The full universal extension asked about in Question 1, interpreted on
positive naturals, including the internal split point of the printed union. -/
def claim : Prop :=
  ∀ α : ℝ, Irrational α → 1 < α → α < (3 + Real.sqrt 5) / 2 →
    ∀ n : ℕ, 1 ≤ n → ∀ x : ℕ, 1 ≤ x →
      (nativeRange α n x ↔ fractionalTest α n x)

/-- At `α = √2`, the positive input and preimage `2` are fixed by the floor
map. Its third iterate therefore contains `2`, but the index-three strict
fractional test fails. This concerns the extension, not the theorem above c. -/
theorem result : ¬ claim := by
  intro h
  have hlo : 1 < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hhi : Real.sqrt 2 < 3 / 2 := Real.sqrt_two_lt_three_halves
  have hpos : 0 < Real.sqrt 2 := lt_trans zero_lt_one hlo
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hupper : Real.sqrt 2 < (3 + Real.sqrt 5) / 2 := by
    linarith [Real.sqrt_nonneg (5 : ℝ)]
  have hfixed : beattySeq (Real.sqrt 2) (2 : ℤ) = 2 := by
    apply Int.floor_eq_iff.mpr
    norm_num
    constructor <;> linarith
  have hmember : nativeRange (Real.sqrt 2) 3 2 := by
    refine ⟨2, by decide, ?_⟩
    exact Function.iterate_fixed hfixed 3
  have htest := ((h (Real.sqrt 2) irrational_sqrt_two hlo hupper
    3 (by decide) 2 (by decide)).mp hmember).2 3 (by decide) (by decide)
  have hfract2 : Int.fract ((2 : ℝ) / Real.sqrt 2 ^ 2) = 0 := by
    rw [hsquare]
    norm_num
  have hdiv3 : (2 : ℝ) / Real.sqrt 2 ^ 3 = 1 / Real.sqrt 2 := by
    rw [pow_succ, hsquare]
    field_simp
  have hfract3 : Int.fract ((2 : ℝ) / Real.sqrt 2 ^ 3) = 1 / Real.sqrt 2 := by
    rw [hdiv3]
    exact Int.fract_eq_self.mpr
      ⟨(one_div_pos.mpr hpos).le, (div_lt_one hpos).mpr hlo⟩
  have hinverse : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    apply (div_eq_iff hpos.ne').mpr
    nlinarith [hsquare]
  have hbad := htest.2
  change Int.fract ((2 : ℝ) / Real.sqrt 2 ^ 3) -
    Int.fract ((2 : ℝ) / Real.sqrt 2 ^ 2) / Real.sqrt 2 < 1 - 1 / Real.sqrt 2 at hbad
  rw [hfract3, hfract2, zero_div, sub_zero, hinverse] at hbad
  linarith

end D5.S3.Arith.Beatty.IteratedBeattyRangeRefutation
