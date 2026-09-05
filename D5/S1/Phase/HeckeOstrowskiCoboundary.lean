/- GID: D5/S1/Phase/HeckeOstrowskiCoboundary
   generality: G
   mirror-B: D5/B/S1/Phase/HeckeOstrowskiCoboundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An interval discrepancy is an explicit coboundary for rotation by alpha. -/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/- Library-search and duplication audit (2026-09-05):
   * D5, digestion, digest, git-history, and in-flight searches for Hecke--
     Ostrowski transfer functions, fractional-part coboundaries, and rotation
     indicators found no existing equivalent declaration.
   * Pinned Mathlib supplies `Int.fract_eq_iff`, `Int.fract_nonneg`, and
     `Int.fract_lt_one`; these prove the two branches of fractional-part
     subtraction without assuming irrationality.
   * `Finset.sum_range_succ` supports the finite telescoping step. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Phase.HeckeOstrowskiCoboundary

open scoped BigOperators

/-- The finite transfer function attached to the interval of length `{q * α}`. -/
noncomputable def transferFunction (α : ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range q, Int.fract (x - (j + 1) * α)

/-- Fractional-part subtraction has exactly one carry, detected by the order
of the two fractional parts. -/
theorem fract_sub_eq_ite (x t : ℝ) :
    Int.fract (x - t) =
      if Int.fract x < Int.fract t then
        Int.fract x + 1 - Int.fract t
      else
        Int.fract x - Int.fract t := by
  split_ifs with h
  · apply Int.fract_eq_iff.mpr
    refine ⟨?_, ?_, ⌊x⌋ - ⌊t⌋ - 1, ?_⟩
    · linarith [Int.fract_nonneg x, Int.fract_lt_one t]
    · linarith
    · push_cast
      linarith [Int.fract_sub_self x, Int.fract_sub_self t]
  · apply Int.fract_eq_iff.mpr
    refine ⟨?_, ?_, ⌊x⌋ - ⌊t⌋, ?_⟩
    · linarith [le_of_not_gt h]
    · linarith [Int.fract_lt_one x, Int.fract_nonneg t]
    · push_cast
      linarith [Int.fract_sub_self x, Int.fract_sub_self t]

private theorem transferFunction_succ (α : ℝ) (q : ℕ) (x : ℝ) :
    transferFunction α (q + 1) x =
      transferFunction α q x + Int.fract (x - (q + 1) * α) := by
  simp [transferFunction, Finset.sum_range_succ]

private theorem transferFunction_difference (α : ℝ) (q : ℕ) (x : ℝ) :
    transferFunction α q x - transferFunction α q (x + α) =
      Int.fract (x - q * α) - Int.fract x := by
  induction q with
  | zero => simp [transferFunction]
  | succ q ih =>
      rw [transferFunction_succ, transferFunction_succ]
      push_cast
      rw [show x + α - ((q : ℝ) + 1) * α = x - q * α by ring]
      linarith [ih]

/-- The centered indicator of `[0, {qα})` is a coboundary for rotation by
`α`, with an explicit finite transfer function. -/
theorem hecke_ostrowski_coboundary (α : ℝ) (q : ℕ) (x : ℝ) :
    (if Int.fract x < Int.fract (q * α) then 1 else 0) -
        Int.fract (q * α) =
      transferFunction α q x - transferFunction α q (x + α) := by
  rw [transferFunction_difference, fract_sub_eq_ite]
  split_ifs <;> ring

#print axioms fract_sub_eq_ite
#print axioms hecke_ostrowski_coboundary

end D5.S1.Phase.HeckeOstrowskiCoboundary
