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
    Prod.mk.injEq, ite_and, Finset.sum_ite_irrel, mul_ite]

private theorem pmf_sum_real {Z : Type*} [Fintype Z] (p : PMF Z) :
    ∑ z, (p z).toReal = 1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  simpa only [tsum_fintype, ENNReal.toReal_sum (fun z _ => p.apply_ne_top z),
    ENNReal.toReal_one] using h

private theorem exp_neg_chord {C x : ℝ} (hC : 0 < C) (hx0 : 0 ≤ x) (hxC : x ≤ C) :
    Real.exp (-x / C) ≤ 1 - (1 - Real.exp (-1)) / C * x := by
  have ht0 : 0 ≤ x / C := div_nonneg hx0 hC.le
  have ht1 : x / C ≤ 1 := (div_le_one hC).2 hxC
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
    (show 0 ≤ 1 - x / C by linarith) ht0 (show (1 - x / C) + x / C = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_neg_one, Real.exp_zero, mul_one] at h
  convert h using 1 <;> congr 1 <;> ring

/-- The uniform contraction factor at inverse scale C. -/
def rate (μ C : ℝ) : ℝ := 1 - μ / C * (1 - Real.exp (-1))

/-- The positive linear clock threshold. -/
def slope (μ C : ℝ) : ℝ := -(C / 2) * Real.log (rate μ C)

/-- The geometric low-clock tail factor. -/
def tailRate (μ C : ℝ) : ℝ := Real.sqrt (rate μ C)

private theorem row_laplace {Z : Type*} [Fintype Z] (p : PMF Z)
    (c : Z → ℝ) {μ C : ℝ} (hC : 0 < C)
    (hc : ∀ z, 0 ≤ c z ∧ c z ≤ C) (hd : μ ≤ ∑ z, (p z).toReal * c z) :
    ∑ z, (p z).toReal * Real.exp (-c z / C) ≤ rate μ C := by
  have he : 0 ≤ (1 - Real.exp (-1)) / C :=
    div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))) hC.le
  calc
    _ ≤ ∑ z, (p z).toReal * (1 - (1 - Real.exp (-1)) / C * c z) :=
      Finset.sum_le_sum fun z _ =>
        mul_le_mul_of_nonneg_left (exp_neg_chord hC (hc z).1 (hc z).2) ENNReal.toReal_nonneg
    _ = 1 - (1 - Real.exp (-1)) / C * ∑ z, (p z).toReal * c z := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [pmf_sum_real, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ 1 - (1 - Real.exp (-1)) / C * μ := by gcongr
    _ = rate μ C := by unfold rate; ring

/-- Every forced adaptive query table has geometric Laplace decay under a
uniform conditional drift bound at every full history and source action. -/
theorem adaptive_laplace_decay
    (κ : ∀ n, Record A Y n → A → PMF Y) (π : Policy A Y)
    (c : ∀ n, Record A Y n → A → Y → ℝ)
    {μ C : ℝ} (hμ : 0 < μ) (hμC : μ ≤ C)
    (hc : ∀ n h a y, 0 ≤ c n h a y ∧ c n h a y ≤ C)
    (hd : ∀ n h a, μ ≤ ∑ y, (κ n h a y).toReal * c n h a y)
    (n : ℕ) :
    ∑ h, (historyLaw κ π n h).toReal * Real.exp (-clock c n h / C) ≤ rate μ C ^ n := by
  classical
  have hC : 0 < C := lt_of_lt_of_le hμ hμC
  have hr : 0 ≤ rate μ C := by
    have he := Real.exp_pos (-1)
    have he1 := Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0)
    have hm : μ / C ≤ 1 := (div_le_one hC).mpr hμC
    have hm0 : 0 ≤ μ / C := div_nonneg hμ.le hC.le
    dsimp [rate]
    nlinarith
  induction n with
  | zero => simp [historyLaw, clock, PMF.pure_apply]
  | succ n ih =>
      simp only [Record, Fintype.sum_prod_type, clock, neg_add, add_div, Real.exp_add]
      calc
        _ = ∑ h, (historyLaw κ π n h).toReal * Real.exp (-clock c n h / C) *
            (∑ a, (π n h a).toReal * ∑ y, (κ n h a y).toReal *
              Real.exp (-c n h a y / C)) := by
          apply Finset.sum_congr rfl
          intro h _
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro y _
          rw [history_law_succ, ENNReal.toReal_mul, ENNReal.toReal_mul]
          ring
        _ ≤ ∑ h, (historyLaw κ π n h).toReal * Real.exp (-clock c n h / C) *
            rate μ C := by
          apply Finset.sum_le_sum
          intro h _
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
          calc
            _ ≤ ∑ a, (π n h a).toReal * rate μ C :=
              Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
                (row_laplace (κ n h a) (c n h a) hC (hc n h a) (hd n h a))
                ENNReal.toReal_nonneg
            _ = rate μ C := by rw [← Finset.sum_mul, pmf_sum_real, one_mul]
        _ = (∑ h, (historyLaw κ π n h).toReal * Real.exp (-clock c n h / C)) *
            rate μ C := (Finset.sum_mul ..).symm
        _ ≤ rate μ C ^ n * rate μ C := mul_le_mul_of_nonneg_right ih hr
        _ = rate μ C ^ (n + 1) := (pow_succ ..).symm

end D5.S3.Observer.ProbabilisticClosure.ConditionalClockMomentComparison
