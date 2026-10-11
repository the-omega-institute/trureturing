/- GID: D5/S3/Observer/ProbabilisticClosure/ConditionalClockMomentComparison
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/ConditionalClockMomentComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Analysis/Convex/SpecificFunctions/Basic]
   utility: none
   digest: Conditional positive clock drift controls adaptive acquisition tails. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SharpChallengeInstrument
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals

noncomputable section

open scoped ENNReal BigOperators
open MeasureTheory ProbabilityTheory
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SharpChallengeInstrument

namespace D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison

variable {A Y : Type} [Fintype A] [Fintype Y]

/-- The actual history law for history-dependent source rows and a common adaptive policy.
A world and a request are fixed parameters of the source rows, not of the policy. -/
def historyLaw (κ : ∀ n, Record A Y n → A → PMF Y) (π : Policy A Y) :
    (n : ℕ) → PMF (Record A Y n)
  | 0 => PMF.pure ()
  | n + 1 => (historyLaw κ π n).bind fun h =>
      (π n h).bind fun a => (κ n h a).map fun y => (h, a, y)

/-- The actual additive clock on a complete finite acquired history. -/
def clock (c : ∀ n, Record A Y n → A → Y → ℝ) : (n : ℕ) → Record A Y n → ℝ
  | 0, _ => 0
  | n + 1, h => clock c n h.1 + c n h.1 h.2.1 h.2.2

private theorem history_law_succ (κ : ∀ n, Record A Y n → A → PMF Y)
    (π : Policy A Y) (n : ℕ) (h : Record A Y n) (a : A) (y : Y) :
    historyLaw κ π (n + 1) (h, a, y) =
      historyLaw κ π n h * (π n h a * κ n h a y) := by
  classical
  simp [historyLaw, PMF.bind_apply, PMF.map_apply, tsum_fintype,
    Prod.mk.injEq, mul_ite, Finset.sum_ite_irrel]

private theorem pmf_sum_real {Z : Type*} [Fintype Z] (p : PMF Z) :
    ∑ z, (p z).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun z _ => p.apply_ne_top z), ← tsum_fintype, p.tsum_coe]
  simp

private theorem exp_neg_chord {C x : ℝ} (hC : 0 < C) (hx0 : 0 ≤ x) (hxC : x ≤ C) :
    Real.exp (-x / C) ≤ 1 - (1 - Real.exp (-1)) / C * x := by
  have ht0 : 0 ≤ x / C := div_nonneg hx0 hC.le
  have ht1 : x / C ≤ 1 := (div_le_one hC).2 hxC
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
    (show 0 ≤ 1 - x / C by linarith) ht0 (show (1 - x / C) + x / C = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_neg_one, Real.exp_zero, mul_one] at h
  convert h using 1 <;> congr 1 <;> ring

end D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison
