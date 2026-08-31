/- GID: D5/S0/Asymptotics/NamingRate/LogarithmicMargin
   generality: G
   mirror-B: D5/B/S0/Asymptotics/NamingRate/LogarithmicMargin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A logarithmic margin turns fast-implies-long into short-implies-slow. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Filter
open scoped Topology

namespace D5.S0.Asymptotics.NamingRate.LogarithmicMargin

/-- A valid witness is fast at length `length` when its running time is within
the prescribed time bound. -/
def IsFastWitness {Witness : Type*}
    (implements : ℕ → Witness → Prop)
    (runningTime : ℕ → Witness → ℕ)
    (timeBound : ℕ → ℕ)
    (length : ℕ) (witness : Witness) : Prop :=
  implements length witness ∧ runningTime length witness ≤ timeBound length

/-- A witness has a long bounded name when its naming cost reaches the
half-length lower bound after the logarithmic error is removed. -/
def HasLongName {Witness : Type*}
    (boundedNameCost : ℕ → Witness → ℕ)
    (error : ℕ → ℝ)
    (length : ℕ) (witness : Witness) : Prop :=
  (length : ℝ) / 2 - error length ≤ boundedNameCost length witness

/-- A valid witness has a short bounded name when its naming cost is at most
one quarter of the input length. -/
def HasShortName {Witness : Type*}
    (implements : ℕ → Witness → Prop)
    (boundedNameCost : ℕ → Witness → ℕ)
    (length : ℕ) (witness : Witness) : Prop :=
  implements length witness ∧
    (boundedNameCost length witness : ℝ) ≤ (length : ℝ) / 4

/-- A witness is slow at length `length` when its running time exceeds the
prescribed time bound. -/
def IsSlowWitness {Witness : Type*}
    (runningTime : ℕ → Witness → ℕ)
    (timeBound : ℕ → ℕ)
    (length : ℕ) (witness : Witness) : Prop :=
  timeBound length < runningTime length witness

/-- An `O(log n)` error is eventually strictly smaller than the gap between
`n / 2` and `n / 4`. -/
private theorem eventual_quarter_margin
    (error : ℕ → ℝ)
    (herror : error =O[atTop] fun n : ℕ => Real.log n) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / 2 - error n > (n : ℝ) / 4 := by
  have hlog :
      (fun n : ℕ => Real.log n) =o[atTop] fun n : ℕ => (n : ℝ) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hsmall := herror.trans_isLittleO hlog
  filter_upwards
    [hsmall.bound (show (0 : ℝ) < 1 / 8 by norm_num), eventually_gt_atTop 0]
      with n hn hn_pos
  have hn_pos_real : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have herror_le : error n ≤ (1 / 8 : ℝ) * n := by
    calc
      error n ≤ ‖error n‖ := Real.le_norm_self _
      _ ≤ (1 / 8 : ℝ) * ‖(n : ℝ)‖ := hn
      _ = (1 / 8 : ℝ) * n := by rw [Real.norm_of_nonneg hn_pos_real.le]
  linarith

/-- If every fast valid witness has a bounded name reaching the half-length
lower bound, then every sufficiently long quarter-short valid witness is slow;
the strict logarithmic quarter-margin is exposed with that contrapositive. -/
theorem logarithmic_error_eventually_leaves_quarter_margin
    {Witness : Type*}
    (implements : ℕ → Witness → Prop)
    (runningTime : ℕ → Witness → ℕ)
    (timeBound : ℕ → ℕ)
    (boundedNameCost : ℕ → Witness → ℕ)
    (error : ℕ → ℝ)
    (herror : error =O[atTop] fun n : ℕ => Real.log n)
    (hfastLong :
      ∀ length witness,
        IsFastWitness implements runningTime timeBound length witness →
          HasLongName boundedNameCost error length witness) :
    ∀ᶠ length : ℕ in atTop,
      (length : ℝ) / 2 - error length > (length : ℝ) / 4 ∧
        ∀ witness,
          HasShortName implements boundedNameCost length witness →
            IsSlowWitness runningTime timeBound length witness := by
  filter_upwards [eventual_quarter_margin error herror] with length hmargin
  refine ⟨hmargin, ?_⟩
  intro witness hshort
  change timeBound length < runningTime length witness
  by_contra hnotSlow
  have hfast :
      IsFastWitness implements runningTime timeBound length witness := by
    refine ⟨hshort.1, ?_⟩
    exact Nat.le_of_not_gt hnotSlow
  have hlong := hfastLong length witness hfast
  change (length : ℝ) / 2 - error length ≤
    (boundedNameCost length witness : ℝ) at hlong
  exact (not_lt_of_ge hlong) (lt_of_le_of_lt hshort.2 hmargin)

#print axioms logarithmic_error_eventually_leaves_quarter_margin

end D5.S0.Asymptotics.NamingRate.LogarithmicMargin
