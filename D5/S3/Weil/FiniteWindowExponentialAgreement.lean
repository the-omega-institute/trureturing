/- GID: D5/S3/Weil/FiniteWindowExponentialAgreement
   generality: G
   mirror-B: D5/B/S3/Weil/FiniteWindowExponentialAgreement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hyperbolic budget tubes force uniform exponential agreement on every fixed window. -/

import D5.S3.Weil.Budget.ExplicitHyperbolicDegreeThreshold
import D5.S3.Weil.ZetaGamma.HyperbolicBudgetTube

/- Library-search audit trail (2026-09-02):
   * Six-route repository searches covered `finite window`, `uniform agreement`,
     `csch`, `cosh`, arbitrary readout families, theorem bodies, digestion
     receipts, and all in-flight lane commits. No theorem packages the local
     correlation law into a uniform-in-time exponential estimate.
   * `HyperbolicBudgetTube.hyperbolic_budget_tube` is the exact frozen owner of
     the two budget walls and is reused rather than reproved.
   * Pinned Mathlib supplies `Real.cosh_le_cosh`, `Real.cosh_sq_sub_sinh_sq`,
     `Real.tanh_eq_sinh_div_cosh`, and the exponential identities. The public
     D5 wrapper `exp_quarter_le_sinh` supplies the eventual lower exponential
     bound for `sinh`; no exact finite-window theorem was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter

namespace D5.S3.Weil.FiniteWindowExponentialAgreement

open D5.S3.Weil.Budget.ExplicitHyperbolicDegreeThreshold
open D5.S3.Weil.ZetaGamma.HyperbolicBudgetTube

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

private theorem inv_sinh_sq_le_exp {x : Real} (xAtLeastOne : 1 <= x) :
    1 / Real.sinh x ^ 2 <= 16 * Real.exp (-2 * x) := by
  have xPositive : 0 < x := lt_of_lt_of_le zero_lt_one xAtLeastOne
  have sinhPositive : 0 < Real.sinh x := Real.sinh_pos_iff.mpr xPositive
  have exponentialLower : Real.exp x / 4 <= Real.sinh x :=
    exp_quarter_le_sinh xAtLeastOne
  have squareLower : (Real.exp x / 4) ^ 2 <= Real.sinh x ^ 2 := by
    nlinarith [Real.exp_pos x]
  have exponentialCancellation : Real.exp (-2 * x) * Real.exp x ^ 2 = 1 := by
    calc
      Real.exp (-2 * x) * Real.exp x ^ 2 =
          Real.exp (-2 * x) * (Real.exp x * Real.exp x) := by ring
      _ = Real.exp (-2 * x) * Real.exp (x + x) := by rw [Real.exp_add]
      _ = Real.exp (-2 * x + (x + x)) :=
        (Real.exp_add (-2 * x) (x + x)).symm
      _ = 1 := by
        rw [show -2 * x + (x + x) = 0 by ring, Real.exp_zero]
  apply (div_le_iff₀ (sq_pos_of_pos sinhPositive)).2
  calc
    1 = 16 * Real.exp (-2 * x) * (Real.exp x / 4) ^ 2 := by
      rw [div_pow]
      nlinarith
    _ <= 16 * Real.exp (-2 * x) * Real.sinh x ^ 2 :=
      mul_le_mul_of_nonneg_left squareLower (by positivity)

private theorem budget_deviation_le_csch_sq
    {Completion : Type*}
    (L a Rstar : Real)
    (budget : Completion -> Real)
    (correlation : Completion -> Real -> Real)
    (globalCompletion localCompletion : Completion)
    (scalePositive : 0 < L)
    (resolventPositive : 0 < a)
    (globalBudget : budget globalCompletion = Rstar)
    (globalBudgetNonnegative : 0 <= Rstar)
    (correlationBound : forall completion t,
      |correlation completion t| <= budget completion)
    (completionDifference : forall t, |t| < 2 * L ->
      correlation localCompletion t - correlation globalCompletion t =
        (budget localCompletion - budget globalCompletion) * Real.cosh (a * t)) :
    |budget localCompletion - Rstar| <=
      Rstar / Real.sinh (a * L) ^ 2 := by
  have tube := hyperbolic_budget_tube L a budget correlation
    globalCompletion localCompletion scalePositive resolventPositive
    correlationBound completionDifference
  rw [globalBudget] at tube
  let x := a * L
  have xPositive : 0 < x := mul_pos resolventPositive scalePositive
  have xNonzero : x ≠ 0 := xPositive.ne'
  have sinhPositive : 0 < Real.sinh x := Real.sinh_pos_iff.mpr xPositive
  have coshPositive : 0 < Real.cosh x := Real.cosh_pos x
  have upperDeviation : budget localCompletion - Rstar <=
      Rstar / Real.sinh x ^ 2 := by
    calc
      budget localCompletion - Rstar <=
          Rstar * (Real.cosh x / Real.sinh x) ^ 2 - Rstar := by
        linarith [tube.2]
      _ = Rstar * ((Real.cosh x / Real.sinh x) ^ 2 - 1) := by ring
      _ = Rstar * (1 / Real.sinh x ^ 2) := by
        rw [coth_sq_sub_one x xNonzero]
      _ = Rstar / Real.sinh x ^ 2 := by ring
  have lowerDeviationCosh : Rstar - budget localCompletion <=
      Rstar / Real.cosh x ^ 2 := by
    calc
      Rstar - budget localCompletion <=
          Rstar - Rstar * Real.tanh x ^ 2 := by
        linarith [tube.1]
      _ = Rstar * (1 - Real.tanh x ^ 2) := by ring
      _ = Rstar * (1 / Real.cosh x ^ 2) := by rw [one_sub_tanh_sq]
      _ = Rstar / Real.cosh x ^ 2 := by ring
  have reciprocalComparison : 1 / Real.cosh x ^ 2 <=
      1 / Real.sinh x ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos coshPositive)
      (sq_pos_of_pos sinhPositive)).2
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  have lowerDeviation : Rstar - budget localCompletion <=
      Rstar / Real.sinh x ^ 2 := by
    calc
      Rstar - budget localCompletion <= Rstar / Real.cosh x ^ 2 :=
        lowerDeviationCosh
      _ = Rstar * (1 / Real.cosh x ^ 2) := by ring
      _ <= Rstar * (1 / Real.sinh x ^ 2) :=
        mul_le_mul_of_nonneg_left reciprocalComparison globalBudgetNonnegative
      _ = Rstar / Real.sinh x ^ 2 := by ring
  rw [abs_le]
  constructor
  · linarith
  · simpa only [x] using upperDeviation

private theorem fixed_window_bound
    {Completion : Type*}
    (L a Rstar T : Real)
    (budget : Completion -> Real)
    (correlation : Completion -> Real -> Real)
    (globalCompletion localCompletion : Completion)
    (scalePositive : 0 < L)
    (resolventPositive : 0 < a)
    (globalBudget : budget globalCompletion = Rstar)
    (globalBudgetNonnegative : 0 <= Rstar)
    (windowNonnegative : 0 <= T)
    (windowInside : T < 2 * L)
    (correlationBound : forall completion t,
      |correlation completion t| <= budget completion)
    (completionDifference : forall t, |t| < 2 * L ->
      correlation localCompletion t - correlation globalCompletion t =
        (budget localCompletion - budget globalCompletion) * Real.cosh (a * t)) :
    forall t, |t| <= T ->
      |correlation localCompletion t - correlation globalCompletion t| <=
        Rstar / Real.sinh (a * L) ^ 2 * Real.cosh (a * T) := by
  intro t timeInWindow
  have timeInside : |t| < 2 * L := timeInWindow.trans_lt windowInside
  have deviation := budget_deviation_le_csch_sq L a Rstar budget correlation
    globalCompletion localCompletion scalePositive resolventPositive globalBudget
    globalBudgetNonnegative correlationBound completionDifference
  have coshMonotone : Real.cosh (a * t) <= Real.cosh (a * T) := by
    rw [Real.cosh_le_cosh]
    rw [abs_mul, abs_mul, abs_of_pos resolventPositive,
      abs_of_nonneg windowNonnegative]
    exact mul_le_mul_of_nonneg_left timeInWindow resolventPositive.le
  have coefficientNonnegative :
      0 <= Rstar / Real.sinh (a * L) ^ 2 := by positivity
  rw [completionDifference t timeInside, globalBudget, abs_mul,
    abs_of_pos (Real.cosh_pos (a * t))]
  exact (mul_le_mul_of_nonneg_right deviation (Real.cosh_pos _).le).trans
    (mul_le_mul_of_nonneg_left coshMonotone coefficientNonnegative)

/-- Under the source's local `cosh` law and zero-lag correlation bound, every
fixed compact window has the `csch^2(aL)` error bound. Moreover one constant,
independent of time in the window, gives eventual `exp (-2*a*L)` decay; at
`a = 1/2` the same statement is exactly eventual `exp (-L)` decay. -/
theorem finite_window_exponential_agreement
    {Completion : Real -> Type*}
    (a Rstar T : Real)
    (budget : forall L, Completion L -> Real)
    (correlation : forall L, Completion L -> Real -> Real)
    (globalCompletion localCompletion : forall L, Completion L)
    (resolventPositive : 0 < a)
    (globalBudgetNonnegative : 0 <= Rstar)
    (windowNonnegative : 0 <= T)
    (globalBudget : forall L, budget L (globalCompletion L) = Rstar)
    (correlationBound : forall L completion t,
      |correlation L completion t| <= budget L completion)
    (completionDifference : forall L t, |t| < 2 * L ->
      correlation L (localCompletion L) t -
          correlation L (globalCompletion L) t =
        (budget L (localCompletion L) - budget L (globalCompletion L)) *
          Real.cosh (a * t)) :
    (forall L, 0 < L -> T < 2 * L -> forall t, |t| <= T ->
      |correlation L (localCompletion L) t -
          correlation L (globalCompletion L) t| <=
        Rstar / Real.sinh (a * L) ^ 2 * Real.cosh (a * T)) /\
    (exists C : Real, 0 <= C /\ ∀ᶠ L in atTop, forall t, |t| <= T ->
      |correlation L (localCompletion L) t -
          correlation L (globalCompletion L) t| <=
        C * Real.exp (-2 * a * L)) /\
    (a = 1 / 2 -> exists C : Real, 0 <= C /\
      ∀ᶠ L in atTop, forall t, |t| <= T ->
        |correlation L (localCompletion L) t -
            correlation L (globalCompletion L) t| <=
          C * Real.exp (-L)) := by
  have pointwise : forall L, 0 < L -> T < 2 * L -> forall t, |t| <= T ->
      |correlation L (localCompletion L) t -
          correlation L (globalCompletion L) t| <=
        Rstar / Real.sinh (a * L) ^ 2 * Real.cosh (a * T) := by
    intro L scalePositive windowInside
    exact fixed_window_bound L a Rstar T (budget L) (correlation L)
      (globalCompletion L) (localCompletion L) scalePositive resolventPositive
      (globalBudget L) globalBudgetNonnegative windowNonnegative windowInside
      (correlationBound L) (completionDifference L)
  let C := 16 * Rstar * Real.cosh (a * T)
  have constantNonnegative : 0 <= C := by
    dsimp [C]
    positivity
  have uniformExponential : ∀ᶠ L in atTop, forall t, |t| <= T ->
      |correlation L (localCompletion L) t -
          correlation L (globalCompletion L) t| <=
        C * Real.exp (-2 * a * L) := by
    filter_upwards [eventually_ge_atTop
      (max (1 / a) ((T + 1) / 2))] with L scaleLarge
    have reciprocalThreshold : 1 / a <= L :=
      (le_max_left _ _).trans scaleLarge
    have argumentAtLeastOne : 1 <= a * L := by
      have := (div_le_iff₀ resolventPositive).mp reciprocalThreshold
      nlinarith
    have scalePositive : 0 < L := by
      have argumentPositive : 0 < a * L := zero_lt_one.trans_le argumentAtLeastOne
      exact pos_of_mul_pos_right argumentPositive resolventPositive.le
    have windowInside : T < 2 * L := by
      have halfThreshold : (T + 1) / 2 <= L :=
        (le_max_right _ _).trans scaleLarge
      linarith
    intro t timeInWindow
    have localBound := pointwise L scalePositive windowInside t timeInWindow
    have decayBound := inv_sinh_sq_le_exp argumentAtLeastOne
    calc
      |correlation L (localCompletion L) t -
          correlation L (globalCompletion L) t| <=
          Rstar / Real.sinh (a * L) ^ 2 * Real.cosh (a * T) := localBound
      _ = (Rstar * Real.cosh (a * T)) *
          (1 / Real.sinh (a * L) ^ 2) := by ring
      _ <= (Rstar * Real.cosh (a * T)) *
          (16 * Real.exp (-2 * (a * L))) :=
        mul_le_mul_of_nonneg_left decayBound (by positivity)
      _ = C * Real.exp (-2 * a * L) := by
        dsimp [C]
        ring
  refine ⟨pointwise, ⟨C, constantNonnegative, uniformExponential⟩, ?_⟩
  intro halfResolvent
  refine ⟨C, constantNonnegative, ?_⟩
  filter_upwards [uniformExponential] with L bound
  intro t timeInWindow
  have := bound t timeInWindow
  rw [halfResolvent] at this
  convert this using 1 <;> ring

/-- The analytic envelope has an explicit equality case at the edge of every
nonnegative window, so the pointwise inequality above is not a vacuous
one-sided assertion. -/
example (a Rstar L T : Real) (resolventPositive : 0 < a)
    (scalePositive : 0 < L) (globalBudgetNonnegative : 0 <= Rstar)
    (_windowNonnegative : 0 <= T) :
    let coefficient := Rstar / Real.sinh (a * L) ^ 2
    let globalCorrelation : Real -> Real := fun _ => 0
    let localCorrelation : Real -> Real := fun t => coefficient * Real.cosh (a * t)
    (forall t, localCorrelation t - globalCorrelation t =
      coefficient * Real.cosh (a * t)) /\
    |localCorrelation T - globalCorrelation T| =
      coefficient * Real.cosh (a * T) := by
  dsimp only
  constructor
  · intro t
    ring
  · rw [sub_zero, abs_mul, abs_of_pos (Real.cosh_pos _)]
    have sinhPositive : 0 < Real.sinh (a * L) :=
      Real.sinh_pos_iff.mpr (mul_pos resolventPositive scalePositive)
    rw [abs_of_nonneg]
    positivity

#print axioms finite_window_exponential_agreement

end D5.S3.Weil.FiniteWindowExponentialAgreement
