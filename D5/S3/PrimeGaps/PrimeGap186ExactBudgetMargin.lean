/- GID: D5/S3/PrimeGaps/PrimeGap186ExactBudgetMargin
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the exact rational safety margin and its conditional real-valued transfer after a certified physical loss budget. -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Exact physical-budget margin

Arithmetic inputs are transcribed from the PrimeGaps186 source audited at
`61340d0b74163003b32756bb16e91d9209a5e330` and the six bound-table budget totals
recorded in this research lane.

This file proves arithmetic and a conditional transfer theorem. It does not
prove any of the 152 upstream physical integral inequalities. In particular,
`hJ`, `hIupper`, and `hloss` below are genuine hypotheses, not discharged
numerical certificates. The numerical functional must also be connected to
the actual sieve theorem before deriving a prime-gap result.

There are 97 source components: 52 outer and 45 inner. Each outer component
requires two analytic bounds, so the analytic ledger still has 152 cells.
No custom axiom, placeholder proof, or native decision procedure is used.
-/

namespace D5.S3.PrimeGaps.PrimeGap186ExactBudgetMargin

/-- The source's distribution parameter after its explicit safety decrement. -/
def rhoStar : ℚ := 2624989 / 10000000

/-- Reference denominator used to normalize the component bounds. -/
def referenceI : ℚ := 23685317816 / (10 : ℚ) ^ 24

/-- Upper bound requested for the physical denominator. -/
def upperI : ℚ := 23685317890 / (10 : ℚ) ^ 24

/-- Lower bound requested for the signed physical numerator. -/
def lowerJ : ℚ := 90248755123 / (10 : ℚ) ^ 24

/-- Sum of the six recorded upward-rounded budget numerators. This declaration
records their arithmetic sum, not a proof that the physical integrals meet it. -/
def totalBudgetNumerator : ℕ :=
  38927522 + 622829241 + 55254 + 435544 + 1405159 + 32422390

/-- The budget is expressed in units of 10^-12 relative to `referenceI`. -/
def lossBudget : ℚ := (totalBudgetNumerator : ℚ) / (10 : ℚ) ^ 12

/-- Exact check of the recorded aggregate budget. -/
theorem totalBudgetNumerator_eq : totalBudgetNumerator = 696075110 := by
  norm_num [totalBudgetNumerator]

/-- Correct source-component count; it is distinct from the analytic-cell count. -/
theorem source_component_count : 17 + 35 + 7 + 10 + 11 + 17 = (97 : ℕ) := by
  norm_num

/-- Each of the 52 outer components has both a root and a face inequality. -/
theorem analytic_cell_count :
    2 * (17 + 35) + 7 + 10 + 11 + 17 + 3 = (152 : ℕ) := by
  norm_num

/-- A strict safety margin of twenty parts per million survives the full
recorded loss budget. This is an unconditional rational-arithmetic theorem. -/
theorem exact_margin_gt_twenty_ppm :
    (1 : ℚ) + 1 / 50000 <
      rhoStar * (lowerJ - lossBudget * referenceI) / upperI := by
  norm_num [rhoStar, lowerJ, lossBudget, totalBudgetNumerator, referenceI, upperI]

/-- Transfer the exact margin to any real-valued numerator, positive denominator,
and absolute loss satisfying the stated bounds. The integral hypotheses remain
explicit. This theorem alone does not establish the upstream numerical input. -/
theorem physical_objective_gt_one_plus_twenty_ppm
    {I J loss : ℝ}
    (hI : 0 < I)
    (hIupper : I ≤ (upperI : ℝ))
    (hJ : (lowerJ : ℝ) ≤ J)
    (hloss : loss ≤ (lossBudget : ℝ) * (referenceI : ℝ)) :
    (1 : ℝ) + 1 / 50000 < (rhoStar : ℝ) * (J - loss) / I := by
  have hrho : 0 < (rhoStar : ℝ) := by
    norm_num [rhoStar]
  have hmargin :
      ((1 : ℝ) + 1 / 50000) * (upperI : ℝ) <
        (rhoStar : ℝ) * ((lowerJ : ℝ) -
          (lossBudget : ℝ) * (referenceI : ℝ)) := by
    norm_num [rhoStar, upperI, lowerJ, lossBudget, totalBudgetNumerator, referenceI]
  have hnum :
      (rhoStar : ℝ) * ((lowerJ : ℝ) -
        (lossBudget : ℝ) * (referenceI : ℝ)) ≤
      (rhoStar : ℝ) * (J - loss) :=
    mul_le_mul_of_nonneg_left (sub_le_sub hJ hloss) hrho.le
  apply (lt_div_iff₀ hI).2
  calc
    ((1 : ℝ) + 1 / 50000) * I ≤
        ((1 : ℝ) + 1 / 50000) * (upperI : ℝ) :=
      mul_le_mul_of_nonneg_left hIupper (by norm_num)
    _ < (rhoStar : ℝ) * ((lowerJ : ℝ) -
        (lossBudget : ℝ) * (referenceI : ℝ)) := hmargin
    _ ≤ (rhoStar : ℝ) * (J - loss) := hnum

#print axioms totalBudgetNumerator_eq
#print axioms exact_margin_gt_twenty_ppm
#print axioms physical_objective_gt_one_plus_twenty_ppm

end D5.S3.PrimeGaps.PrimeGap186ExactBudgetMargin
