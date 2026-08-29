/- GID: D5/S3/Weil/ZetaGamma/HyperbolicBudgetTube
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaGamma/HyperbolicBudgetTube
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local positive correlations force every resolvent budget into a hyperbolic tube. -/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-29):
   * D5 statement-shape searches for local completion budgets, hyperbolic tubes,
     and real positive-spectrum correlations found no existing theorem.
   * The freshly frozen Weil owners `PositivityChartCollapse`,
     `PrimePoissonResummation`, `ArchimedeanConfinement`,
     `SafeComplementFiniteIndex`, and `CertifiedStickyMatrix` were inspected;
     they provide adjacent positivity and spectral machinery but not this result.
   * Pinned Mathlib provides `Real.cosh_two_mul`,
     `Real.tanh_eq_sinh_div_cosh`, `Real.cosh_sq_sub_sinh_sq`, and closure
     calculus for real intervals.  No `coth`, `csch`, or `sech` definition and
     no exact budget-tube theorem was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaGamma.HyperbolicBudgetTube

open Filter
open Set

private theorem one_sub_tanh_sq (x : Real) :
    1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  field_simp [(Real.cosh_pos x).ne']
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

private theorem coth_sq_sub_one (x : Real) (xNonzero : x ≠ 0) :
    (Real.cosh x / Real.sinh x) ^ 2 - 1 = 1 / Real.sinh x ^ 2 := by
  rw [div_pow]
  have sinhNonzero : Real.sinh x ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact xNonzero
  field_simp [sinhNonzero]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

private theorem inv_cosh_half_sq_eq (L : Real) :
    1 / Real.cosh (L / 2) ^ 2 =
      4 * Real.exp (-L) / (1 + Real.exp (-L)) ^ 2 := by
  have expDouble : Real.exp L = Real.exp (L / 2) ^ 2 := by
    calc
      Real.exp L = Real.exp (L / 2 + L / 2) := by
        congr 1
        ring
      _ = Real.exp (L / 2) * Real.exp (L / 2) := Real.exp_add _ _
      _ = Real.exp (L / 2) ^ 2 := by ring
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_neg, expDouble]
  field_simp [Real.exp_ne_zero]
  ring

private theorem inv_sinh_half_sq_eq (L : Real) (scalePositive : 0 < L) :
    1 / Real.sinh (L / 2) ^ 2 =
      4 * Real.exp (-L) / (1 - Real.exp (-L)) ^ 2 := by
  have expDouble : Real.exp L = Real.exp (L / 2) ^ 2 := by
    calc
      Real.exp L = Real.exp (L / 2 + L / 2) := by
        congr 1
        ring
      _ = Real.exp (L / 2) * Real.exp (L / 2) := Real.exp_add _ _
      _ = Real.exp (L / 2) ^ 2 := by ring
  have expHalfNeOne : Real.exp (L / 2) ≠ 1 := by
    rw [ne_eq, Real.exp_eq_one_iff]
    linarith
  rw [Real.sinh_eq, Real.exp_neg, Real.exp_neg, expDouble]
  field_simp [Real.exp_ne_zero, expHalfNeOne]
  ring

private theorem inv_cosh_half_sq_le_exp (L : Real) :
    1 / Real.cosh (L / 2) ^ 2 <= 4 * Real.exp (-L) := by
  rw [inv_cosh_half_sq_eq]
  let x := Real.exp (-L)
  have xPositive : 0 < x := Real.exp_pos _
  have denominatorPositive : 0 < (1 + x) ^ 2 := by positivity
  apply (div_le_iff₀ denominatorPositive).2
  nlinarith [sq_nonneg x]

private theorem inv_sinh_half_sq_le_exp_refined
    (L : Real) (scaleAtLeastOne : 1 <= L) :
    1 / Real.sinh (L / 2) ^ 2 <=
      4 * Real.exp (-L) + 48 * Real.exp (-2 * L) := by
  have scalePositive : 0 < L := lt_of_lt_of_le zero_lt_one scaleAtLeastOne
  rw [inv_sinh_half_sq_eq L scalePositive]
  let x := Real.exp (-L)
  have xPositive : 0 < x := Real.exp_pos _
  have xAtMostHalf : x <= 1 / 2 := by
    have monotoneBound : Real.exp (-L) <= Real.exp (-1) := by
      rw [Real.exp_le_exp]
      linarith
    exact monotoneBound.trans Real.exp_neg_one_lt_half.le
  have oneMinusPositive : 0 < 1 - x := by linarith
  have quadraticNonnegative : 0 <= 10 - 23 * x + 12 * x ^ 2 := by
    have productNonnegative :
        0 <= (1 - 2 * x) * ((17 : Real) / 2 - 6 * x) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have reciprocalExcess :
      1 / (1 - x) ^ 2 - 1 <= 12 * x := by
    rw [sub_le_iff_le_add]
    apply (div_le_iff₀ (sq_pos_of_pos oneMinusPositive)).2
    nlinarith
  have exponentialSquare : Real.exp (-2 * L) = x ^ 2 := by
    calc
      Real.exp (-2 * L) = Real.exp (-L + -L) := by
        congr 1
        ring
      _ = Real.exp (-L) * Real.exp (-L) := Real.exp_add _ _
      _ = x ^ 2 := by dsimp [x]; ring
  rw [exponentialSquare]
  have scaledExcess :
      4 * x / (1 - x) ^ 2 - 4 * x <= 48 * x ^ 2 := by
    have := mul_le_mul_of_nonneg_left reciprocalExcess (show 0 <= 4 * x by positivity)
    calc
      4 * x / (1 - x) ^ 2 - 4 * x =
          4 * x * (1 / (1 - x) ^ 2 - 1) := by ring
      _ <= 4 * x * (12 * x) := this
      _ = 48 * x ^ 2 := by ring
  nlinarith

/-- If every completion correlation is bounded by its nonnegative zero-lag
budget and two completions differ by the source's local `cosh` law, then the
local budget lies between the two sharp hyperbolic walls around the global
budget.  The quotient `cosh / sinh` is the source's `coth`. -/
theorem hyperbolic_budget_tube
    {Completion : Type*}
    (L a : Real)
    (budget : Completion -> Real)
    (correlation : Completion -> Real -> Real)
    (globalCompletion localCompletion : Completion)
    (scalePositive : 0 < L)
    (resolventPositive : 0 < a)
    (correlationBound : forall completion t,
      |correlation completion t| <= budget completion)
    (completionDifference : forall t, |t| < 2 * L ->
      correlation localCompletion t - correlation globalCompletion t =
        (budget localCompletion - budget globalCompletion) * Real.cosh (a * t)) :
    budget globalCompletion * Real.tanh (a * L) ^ 2 <= budget localCompletion /\
      budget localCompletion <= budget globalCompletion *
        (Real.cosh (a * L) / Real.sinh (a * L)) ^ 2 := by
  have openWindowBound : forall t, t ∈ Ioo (0 : Real) (2 * L) ->
      |budget localCompletion - budget globalCompletion| * Real.cosh (a * t) <=
        budget localCompletion + budget globalCompletion := by
    intro t ht
    have difference := completionDifference t (by
      rw [abs_of_pos ht.1]
      exact ht.2)
    calc
      |budget localCompletion - budget globalCompletion| * Real.cosh (a * t) =
          |(budget localCompletion - budget globalCompletion) * Real.cosh (a * t)| := by
            rw [abs_mul, abs_of_pos (Real.cosh_pos _)]
      _ = |correlation localCompletion t - correlation globalCompletion t| := by
        rw [difference]
      _ <= |correlation localCompletion t| + |correlation globalCompletion t| :=
        abs_sub _ _
      _ <= budget localCompletion + budget globalCompletion :=
        add_le_add (correlationBound localCompletion t)
          (correlationBound globalCompletion t)
  have endpointInClosure : 2 * L ∈ closure (Ioo (0 : Real) (2 * L)) := by
    rw [closure_Ioo (by linarith)]
    exact ⟨by linarith, le_rfl⟩
  have closedBudgetBound : IsClosed
      {t : Real | |budget localCompletion - budget globalCompletion| *
          Real.cosh (a * t) <=
        budget localCompletion + budget globalCompletion} := by
    exact isClosed_le
      (continuous_const.mul (Real.continuous_cosh.comp
        (continuous_const.mul continuous_id)))
      continuous_const
  have endpointBound :
      |budget localCompletion - budget globalCompletion| * Real.cosh (a * (2 * L)) <=
        budget localCompletion + budget globalCompletion := by
    exact (closure_minimal (fun t ht => openWindowBound t ht)
      closedBudgetBound) endpointInClosure
  let x := a * L
  have xPositive : 0 < x := mul_pos resolventPositive scalePositive
  have sinhPositive : 0 < Real.sinh x := Real.sinh_pos_iff.mpr xPositive
  have coshPositive : 0 < Real.cosh x := Real.cosh_pos x
  have endpointBound' :
      |budget localCompletion - budget globalCompletion| *
          (Real.cosh x ^ 2 + Real.sinh x ^ 2) <=
        budget localCompletion + budget globalCompletion := by
    rw [show a * (2 * L) = 2 * x by dsimp [x]; ring,
      Real.cosh_two_mul] at endpointBound
    exact endpointBound
  have hyperbolicFactorNonnegative :
      0 <= Real.cosh x ^ 2 + Real.sinh x ^ 2 := by positivity
  have lowerDifferenceBound :
      (budget globalCompletion - budget localCompletion) *
          (Real.cosh x ^ 2 + Real.sinh x ^ 2) <=
        budget localCompletion + budget globalCompletion := by
    simpa only [neg_sub] using
      (mul_le_mul_of_nonneg_right
        (neg_le_abs (budget localCompletion - budget globalCompletion))
        hyperbolicFactorNonnegative).trans endpointBound'
  have upperDifferenceBound :
      (budget localCompletion - budget globalCompletion) *
          (Real.cosh x ^ 2 + Real.sinh x ^ 2) <=
        budget localCompletion + budget globalCompletion := by
    exact (mul_le_mul_of_nonneg_right
      (le_abs_self (budget localCompletion - budget globalCompletion))
      hyperbolicFactorNonnegative).trans endpointBound'
  have lowerScaled :
      budget globalCompletion * Real.sinh x ^ 2 <=
        budget localCompletion * Real.cosh x ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  have upperScaled :
      budget localCompletion * Real.sinh x ^ 2 <=
        budget globalCompletion * Real.cosh x ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  constructor
  · rw [Real.tanh_eq_sinh_div_cosh, div_pow, ← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos coshPositive)).2
    simpa only [x] using lowerScaled
  · rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos sinhPositive)).2
    simpa only [x] using upperScaled

/-- At the natural central budget `2 * lambdaOne`, the hyperbolic tube controls
the lower and upper budget profiles, their width, and both the leading and
refined exponential errors.  The three local profile functions are constructed
from the range of the source budget on each completion carrier. -/
theorem riemann_budget_tube
    {Completion : Real -> Type*}
    (lambdaOne : Real)
    (budget : forall L, Completion L -> Real)
    (correlation : forall L, Completion L -> Real -> Real)
    (naturalCompletion : forall L, Completion L)
    (lambdaPositive : 0 < lambdaOne)
    (naturalBudget : forall L, budget L (naturalCompletion L) = 2 * lambdaOne)
    (correlationBound : forall L completion t,
      |correlation L completion t| <= budget L completion)
    (completionDifference : forall L completion t, |t| < 2 * L ->
      correlation L completion t - correlation L (naturalCompletion L) t =
        (budget L completion - budget L (naturalCompletion L)) *
          Real.cosh (t / 2)) :
    let lowerBudget := fun L => sInf (Set.range (budget L))
    let upperBudget := fun L => sSup (Set.range (budget L))
    let budgetWidth := fun L => upperBudget L - lowerBudget L
    (forall L, 0 < L -> forall completion,
      2 * lambdaOne * Real.tanh (L / 2) ^ 2 <= budget L completion /\
        budget L completion <= 2 * lambdaOne *
          (Real.cosh (L / 2) / Real.sinh (L / 2)) ^ 2) /\
    (forall L, 0 < L ->
      0 <= 2 * lambdaOne - lowerBudget L /\
        2 * lambdaOne - lowerBudget L <=
          2 * lambdaOne / Real.cosh (L / 2) ^ 2) /\
    (forall L, 0 < L ->
      0 <= upperBudget L - 2 * lambdaOne /\
        upperBudget L - 2 * lambdaOne <=
          2 * lambdaOne / Real.sinh (L / 2) ^ 2) /\
    (fun L => 2 * lambdaOne - lowerBudget L) =O[atTop]
      (fun L => Real.exp (-L)) /\
    (fun L => upperBudget L - 2 * lambdaOne) =O[atTop]
      (fun L => Real.exp (-L)) /\
    budgetWidth =O[atTop] (fun L => Real.exp (-L)) /\
    (fun L => max 0
      (2 * lambdaOne - lowerBudget L - 8 * lambdaOne * Real.exp (-L))) =O[atTop]
        (fun L => Real.exp (-2 * L)) /\
    (fun L => max 0
      (upperBudget L - 2 * lambdaOne - 8 * lambdaOne * Real.exp (-L))) =O[atTop]
        (fun L => Real.exp (-2 * L)) /\
    (fun L => max 0
      (budgetWidth L - 16 * lambdaOne * Real.exp (-L))) =O[atTop]
        (fun L => Real.exp (-2 * L)) := by
  dsimp only
  have tube : forall L, 0 < L -> forall completion,
      2 * lambdaOne * Real.tanh (L / 2) ^ 2 <= budget L completion /\
        budget L completion <= 2 * lambdaOne *
          (Real.cosh (L / 2) / Real.sinh (L / 2)) ^ 2 := by
    intro L scalePositive completion
    have specialized := hyperbolic_budget_tube L (1 / 2 : Real) (budget L)
      (correlation L) (naturalCompletion L) completion scalePositive (by norm_num)
      (correlationBound L) (by
        intro t ht
        simpa only [naturalBudget L, show (1 / 2 : Real) * t = t / 2 by ring] using
          completionDifference L completion t ht)
    simpa only [naturalBudget L, show (1 / 2 : Real) * L = L / 2 by ring] using
      specialized
  have profileBounds : forall L, 0 < L ->
      2 * lambdaOne * Real.tanh (L / 2) ^ 2 <= sInf (Set.range (budget L)) /\
        sInf (Set.range (budget L)) <= 2 * lambdaOne /\
        2 * lambdaOne <= sSup (Set.range (budget L)) /\
        sSup (Set.range (budget L)) <= 2 * lambdaOne *
          (Real.cosh (L / 2) / Real.sinh (L / 2)) ^ 2 := by
    intro L scalePositive
    have lowerBounded : BddBelow (Set.range (budget L)) := by
      refine ⟨2 * lambdaOne * Real.tanh (L / 2) ^ 2, ?_⟩
      rintro value ⟨completion, rfl⟩
      exact (tube L scalePositive completion).1
    have upperBounded : BddAbove (Set.range (budget L)) := by
      refine ⟨2 * lambdaOne *
        (Real.cosh (L / 2) / Real.sinh (L / 2)) ^ 2, ?_⟩
      rintro value ⟨completion, rfl⟩
      exact (tube L scalePositive completion).2
    have rangeNonempty : (Set.range (budget L)).Nonempty :=
      ⟨budget L (naturalCompletion L), Set.mem_range_self _⟩
    refine ⟨le_csInf rangeNonempty ?_, ?_, ?_, csSup_le rangeNonempty ?_⟩
    · rintro value ⟨completion, rfl⟩
      exact (tube L scalePositive completion).1
    · exact (csInf_le lowerBounded (Set.mem_range_self (naturalCompletion L))).trans_eq
        (naturalBudget L)
    · exact (naturalBudget L).symm.le.trans
        (le_csSup upperBounded (Set.mem_range_self (naturalCompletion L)))
    · rintro value ⟨completion, rfl⟩
      exact (tube L scalePositive completion).2
  have lowerError : forall L, 0 < L ->
      0 <= 2 * lambdaOne - sInf (Set.range (budget L)) /\
        2 * lambdaOne - sInf (Set.range (budget L)) <=
          2 * lambdaOne / Real.cosh (L / 2) ^ 2 := by
    intro L scalePositive
    have profile := profileBounds L scalePositive
    constructor
    · linarith
    · calc
        2 * lambdaOne - sInf (Set.range (budget L)) <=
            2 * lambdaOne - 2 * lambdaOne * Real.tanh (L / 2) ^ 2 := by
              linarith [profile.1]
        _ = 2 * lambdaOne * (1 - Real.tanh (L / 2) ^ 2) := by ring
        _ = 2 * lambdaOne * (1 / Real.cosh (L / 2) ^ 2) := by
          rw [one_sub_tanh_sq]
        _ = 2 * lambdaOne / Real.cosh (L / 2) ^ 2 := by ring
  have upperError : forall L, 0 < L ->
      0 <= sSup (Set.range (budget L)) - 2 * lambdaOne /\
        sSup (Set.range (budget L)) - 2 * lambdaOne <=
          2 * lambdaOne / Real.sinh (L / 2) ^ 2 := by
    intro L scalePositive
    have profile := profileBounds L scalePositive
    have halfNonzero : L / 2 ≠ 0 := by linarith
    constructor
    · linarith
    · calc
        sSup (Set.range (budget L)) - 2 * lambdaOne <=
            2 * lambdaOne *
                (Real.cosh (L / 2) / Real.sinh (L / 2)) ^ 2 -
              2 * lambdaOne := by
                linarith [profile.2.2.2]
        _ = 2 * lambdaOne / Real.sinh (L / 2) ^ 2 := by
          calc
            2 * lambdaOne *
                  (Real.cosh (L / 2) / Real.sinh (L / 2)) ^ 2 -
                2 * lambdaOne =
              2 * lambdaOne *
                ((Real.cosh (L / 2) / Real.sinh (L / 2)) ^ 2 - 1) := by ring
            _ = 2 * lambdaOne * (1 / Real.sinh (L / 2) ^ 2) := by
              rw [coth_sq_sub_one _ halfNonzero]
            _ = 2 * lambdaOne / Real.sinh (L / 2) ^ 2 := by ring
  have eventualBounds : ∀ᶠ L in atTop,
      0 <= 2 * lambdaOne - sInf (Set.range (budget L)) /\
      2 * lambdaOne - sInf (Set.range (budget L)) <=
        8 * lambdaOne * Real.exp (-L) /\
      0 <= sSup (Set.range (budget L)) - 2 * lambdaOne /\
      sSup (Set.range (budget L)) - 2 * lambdaOne <=
        8 * lambdaOne * Real.exp (-L) +
          96 * lambdaOne * Real.exp (-2 * L) := by
    filter_upwards [eventually_ge_atTop (1 : Real)] with L scaleAtLeastOne
    have scalePositive : 0 < L := lt_of_lt_of_le zero_lt_one scaleAtLeastOne
    have lower := lowerError L scalePositive
    have upper := upperError L scalePositive
    have lowerDecay := inv_cosh_half_sq_le_exp L
    have upperDecay := inv_sinh_half_sq_le_exp_refined L scaleAtLeastOne
    refine ⟨lower.1, lower.2.trans ?_, upper.1, upper.2.trans ?_⟩
    · calc
        2 * lambdaOne / Real.cosh (L / 2) ^ 2 =
            2 * lambdaOne * (1 / Real.cosh (L / 2) ^ 2) := by ring
        _ <= 2 * lambdaOne * (4 * Real.exp (-L)) :=
          mul_le_mul_of_nonneg_left lowerDecay (by positivity)
        _ = 8 * lambdaOne * Real.exp (-L) := by ring
    · calc
        2 * lambdaOne / Real.sinh (L / 2) ^ 2 =
            2 * lambdaOne * (1 / Real.sinh (L / 2) ^ 2) := by ring
        _ <= 2 * lambdaOne *
            (4 * Real.exp (-L) + 48 * Real.exp (-2 * L)) :=
          mul_le_mul_of_nonneg_left upperDecay (by positivity)
        _ = 8 * lambdaOne * Real.exp (-L) +
            96 * lambdaOne * Real.exp (-2 * L) := by ring
  have lowerBigO : (fun L => 2 * lambdaOne - sInf (Set.range (budget L))) =O[atTop]
      (fun L => Real.exp (-L)) := by
    apply Asymptotics.IsBigO.of_bound (8 * lambdaOne)
    filter_upwards [eventualBounds] with L bounds
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg bounds.1,
      abs_of_pos (Real.exp_pos _)]
    exact bounds.2.1
  have upperBigO : (fun L => sSup (Set.range (budget L)) - 2 * lambdaOne) =O[atTop]
      (fun L => Real.exp (-L)) := by
    apply Asymptotics.IsBigO.of_bound (104 * lambdaOne)
    filter_upwards [eventualBounds, eventually_ge_atTop (1 : Real)] with L bounds scaleAtLeastOne
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg bounds.2.2.1,
      abs_of_pos (Real.exp_pos _)]
    have exponentialComparison : Real.exp (-2 * L) <= Real.exp (-L) := by
      rw [Real.exp_le_exp]
      linarith
    have scaledComparison := mul_le_mul_of_nonneg_left exponentialComparison
      (by positivity : 0 <= 96 * lambdaOne)
    linarith [bounds.2.2.2]
  have widthBigO : (fun L => sSup (Set.range (budget L)) -
      sInf (Set.range (budget L))) =O[atTop] (fun L => Real.exp (-L)) := by
    apply Asymptotics.IsBigO.of_bound (112 * lambdaOne)
    filter_upwards [eventualBounds, eventually_ge_atTop (1 : Real)] with L bounds scaleAtLeastOne
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have widthNonnegative :
        0 <= sSup (Set.range (budget L)) - sInf (Set.range (budget L)) := by
      linarith [bounds.1, bounds.2.2.1]
    rw [abs_of_nonneg widthNonnegative]
    have exponentialComparison : Real.exp (-2 * L) <= Real.exp (-L) := by
      rw [Real.exp_le_exp]
      linarith
    have scaledComparison := mul_le_mul_of_nonneg_left exponentialComparison
      (by positivity : 0 <= 96 * lambdaOne)
    linarith [bounds.2.1, bounds.2.2.2]
  have lowerRefined : (fun L => max 0
      (2 * lambdaOne - sInf (Set.range (budget L)) -
        8 * lambdaOne * Real.exp (-L))) =O[atTop]
      (fun L => Real.exp (-2 * L)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventualBounds] with L bounds
    rw [Real.norm_eq_abs, Real.norm_eq_abs, max_eq_left (by linarith [bounds.2.1]),
      abs_zero, abs_of_pos (Real.exp_pos _)]
    positivity
  have upperRefined : (fun L => max 0
      (sSup (Set.range (budget L)) - 2 * lambdaOne -
        8 * lambdaOne * Real.exp (-L))) =O[atTop]
      (fun L => Real.exp (-2 * L)) := by
    apply Asymptotics.IsBigO.of_bound (96 * lambdaOne)
    filter_upwards [eventualBounds] with L bounds
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _),
      abs_of_pos (Real.exp_pos _)]
    apply max_le
    · positivity
    · linarith [bounds.2.2.2]
  have widthRefined : (fun L => max 0
      (sSup (Set.range (budget L)) - sInf (Set.range (budget L)) -
        16 * lambdaOne * Real.exp (-L))) =O[atTop]
      (fun L => Real.exp (-2 * L)) := by
    apply Asymptotics.IsBigO.of_bound (96 * lambdaOne)
    filter_upwards [eventualBounds] with L bounds
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _),
      abs_of_pos (Real.exp_pos _)]
    apply max_le
    · positivity
    · linarith [bounds.2.1, bounds.2.2.2]
  exact ⟨tube, lowerError, upperError, lowerBigO, upperBigO, widthBigO,
    lowerRefined, upperRefined, widthRefined⟩

#print axioms hyperbolic_budget_tube
#print axioms riemann_budget_tube

end D5.S3.Weil.ZetaGamma.HyperbolicBudgetTube
