/- GID: D5/S3/Estimation/ErrorExponents/BernoulliIntervalThreshold
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:shared-decision-construction)
   anchors: []
   digest: One fixed count threshold controls both testing errors uniformly over separated Bernoulli parameter intervals. -/

import D5.S0.Diagonal.TypicalDensity

/-!
# A single test for interval-uncertain Bernoulli readout

The experiment is Mathlib's existing Binomial count measure. No new probability
law, iid carrier or Bayes optimum is defined. The actual decision is the same
half-line for every pair of parameters in the two intervals. Ties go to the
second hypothesis. The upper and lower KL tails are reused from the repository.
The new bridge is a three-point KL calculation that compares every permitted
parameter to the nearest interval endpoint, and the fixed decision construction.

Audit at e093071699088b3e97584cfb2b53e56923642eff: `bernoulliKL`,
`binomial_lower_tail_kl` and `binomial_upper_tail_kl` already exist. Searches for
common-mode/uniform/minimax draft work found #5750 and its explicit outstanding
quantifier gap, with no matching interval-threshold owner.

This is a constructive uniform risk certificate, not an exact minimax claim.
It treats independent identically distributed shots with an unknown fixed
parameter in (0,1); it does not certify correlated or varying shot probabilities.
Robust-testing context: Gul and Zoubir, arXiv:1502.00647. Their general minimax
theory is not imported as an axiom or re-proved by this special-case construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.ErrorExponents.BernoulliIntervalThreshold

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory unitInterval
open D5.S0.Diagonal.MarginBound
open D5.S0.Diagonal.TypicalDensity

noncomputable section

/-- Fixed count decision: accept the second hypothesis at or above the threshold.
It depends on the planned shot count and threshold, not the unknown parameters. -/
def thresholdEvent (shots : ℕ) (threshold : ℝ) : Set ℝ :=
  Set.Ici (threshold * (shots : ℝ))

/-- Equal-prior risk of this specified decision in the existing count experiment. -/
def thresholdRisk (shots : ℕ) (threshold : ℝ) (p q : Set.Icc (0 : ℝ) 1) : ℝ :=
  (Bin(ℝ, shots, p).real (thresholdEvent shots threshold) +
    Bin(ℝ, shots, q).real (thresholdEvent shots threshold)ᶜ) / 2

private theorem kl_three_point (t u p : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hu0 : 0 < u) (hu1 : u < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    bernoulliKL t p = bernoulliKL t u + bernoulliKL u p +
      (t - u) * ((Real.log u - Real.log p) -
        (Real.log (1 - u) - Real.log (1 - p))) := by
  unfold bernoulliKL
  rw [Real.log_div ht0.ne' hp0.ne',
    Real.log_div (sub_pos.mpr ht1).ne' (sub_pos.mpr hp1).ne',
    Real.log_div ht0.ne' hu0.ne',
    Real.log_div (sub_pos.mpr ht1).ne' (sub_pos.mpr hu1).ne',
    Real.log_div hu0.ne' hp0.ne',
    Real.log_div (sub_pos.mpr hu1).ne' (sub_pos.mpr hp1).ne']
  ring

/-- Below the threshold, the nearest allowed parameter minimizes this KL rate. -/
theorem kl_lower_endpoint_bound (t u p : ℝ)
    (hp0 : 0 < p) (hpu : p ≤ u) (hut : u ≤ t) (ht1 : t < 1) :
    bernoulliKL t u ≤ bernoulliKL t p := by
  have hu0 : 0 < u := hp0.trans_le hpu
  have ht0 : 0 < t := hu0.trans_le hut
  have hu1 : u < 1 := hut.trans_lt ht1
  have hp1 : p < 1 := hpu.trans_lt hu1
  have hd := bernoulliKL_nonneg hu0 hu1 hp0 hp1
  have hlog0 : 0 ≤ Real.log u - Real.log p :=
    sub_nonneg.mpr (Real.log_le_log hp0 hpu)
  have hlog1 : 0 ≤ Real.log (1 - p) - Real.log (1 - u) :=
    sub_nonneg.mpr (Real.log_le_log (sub_pos.mpr hu1) (by linarith))
  have hterm : 0 ≤ (t - u) * ((Real.log u - Real.log p) -
      (Real.log (1 - u) - Real.log (1 - p))) :=
    mul_nonneg (sub_nonneg.mpr hut) (by linarith)
  rw [kl_three_point t u p ht0 ht1 hu0 hu1 hp0 hp1]
  linarith

/-- Above the threshold, the nearest allowed parameter minimizes this KL rate. -/
theorem kl_upper_endpoint_bound (t v q : ℝ)
    (ht0 : 0 < t) (htv : t ≤ v) (hvq : v ≤ q) (hq1 : q < 1) :
    bernoulliKL t v ≤ bernoulliKL t q := by
  have h := kl_lower_endpoint_bound (1-t) (1-v) (1-q)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have ht : 1 - (1 - t) = t := by ring
  have hv : 1 - (1 - v) = v := by ring
  have hq : 1 - (1 - q) = q := by ring
  simpa only [bernoulliKL, ht, hv, hq, add_comm] using h

/-- Both actual error events of one fixed rule are bounded by interval endpoints. -/
theorem shared_threshold_error_bounds (shots : ℕ) (u t v : ℝ)
    (hu0 : 0 < u) (hut : u < t) (htv : t < v) (hv1 : v < 1)
    (p q : Set.Icc (0 : ℝ) 1)
    (hp0 : 0 < (p : ℝ)) (hpu : (p : ℝ) ≤ u)
    (hvq : v ≤ (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    Bin(ℝ, shots, p).real (thresholdEvent shots t) ≤
        Real.exp (-(shots : ℝ) * bernoulliKL t u) ∧
      Bin(ℝ, shots, q).real (thresholdEvent shots t)ᶜ ≤
        Real.exp (-(shots : ℝ) * bernoulliKL t v) := by
  have ht0 : 0 < t := hu0.trans hut
  have ht1 : t < 1 := htv.trans hv1
  have hN : 0 ≤ (shots : ℝ) := Nat.cast_nonneg shots
  constructor
  · have htail := binomial_upper_tail_kl shots (q := t) p hp0
      (hpu.trans_lt hut) ht1
    have hKL := kl_lower_endpoint_bound t u p hp0 hpu hut.le ht1
    have hexp : Real.exp (-(shots : ℝ) * bernoulliKL t p) ≤
        Real.exp (-(shots : ℝ) * bernoulliKL t u) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hKL hN
      linarith
    exact htail.trans hexp
  · have htail := binomial_lower_tail_kl shots (q := t) q ht0
      (htv.trans_le hvq) hq1
    have hKL := kl_upper_endpoint_bound t v q ht0 htv.le hvq hq1
    have hexp : Real.exp (-(shots : ℝ) * bernoulliKL t q) ≤
        Real.exp (-(shots : ℝ) * bernoulliKL t v) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hKL hN
      linarith
    have hsubset : (thresholdEvent shots t)ᶜ ⊆ {x : ℝ | x ≤ t * shots} := by
      intro x hx
      change ¬ t * (shots : ℝ) ≤ x at hx
      exact (lt_of_not_ge hx).le
    exact (measureReal_mono hsubset).trans (htail.trans hexp)

/-- This is the changed quantifier: choose the event once, then vary both laws. -/
theorem exists_one_test_for_all_parameters (shots : ℕ) (u t v : ℝ)
    (hu0 : 0 < u) (hut : u < t) (htv : t < v) (hv1 : v < 1) :
    ∃ event : Set ℝ, MeasurableSet event ∧
      ∀ p q : Set.Icc (0 : ℝ) 1,
        0 < (p : ℝ) → (p : ℝ) ≤ u → v ≤ (q : ℝ) → (q : ℝ) < 1 →
        (Bin(ℝ, shots, p).real event + Bin(ℝ, shots, q).real eventᶜ) / 2 ≤
          (Real.exp (-(shots : ℝ) * bernoulliKL t u) +
            Real.exp (-(shots : ℝ) * bernoulliKL t v)) / 2 := by
  refine ⟨thresholdEvent shots t, measurableSet_Ici, ?_⟩
  intro p q hp0 hpu hvq hq1
  have h := shared_threshold_error_bounds shots u t v hu0 hut htv hv1
    p q hp0 hpu hvq hq1
  linarith [h.1, h.2]

/-- Conservative common exponent for the specified count rule. -/
def thresholdRate (u t v : ℝ) : ℝ := min (bernoulliKL t u) (bernoulliKL t v)

/-- Any strict gap with a strictly interior threshold gives a positive rate. -/
theorem threshold_rate_pos (u t v : ℝ)
    (hu0 : 0 < u) (hut : u < t) (htv : t < v) (hv1 : v < 1) :
    0 < thresholdRate u t v := by
  have ht0 : 0 < t := hu0.trans hut
  have ht1 : t < 1 := htv.trans hv1
  exact lt_min
    (bernoulliKL_pos ht0 ht1 hu0 (hut.trans ht1) (ne_of_gt hut))
    (bernoulliKL_pos ht0 ht1 (ht0.trans htv) hv1 (ne_of_lt htv))

/-- A uniform exponential bound for the actual fixed decision, not an optimum. -/
theorem threshold_risk_le_exponential (shots : ℕ) (u t v : ℝ)
    (hu0 : 0 < u) (hut : u < t) (htv : t < v) (hv1 : v < 1)
    (p q : Set.Icc (0 : ℝ) 1)
    (hp0 : 0 < (p : ℝ)) (hpu : (p : ℝ) ≤ u)
    (hvq : v ≤ (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    thresholdRisk shots t p q ≤ Real.exp (-(shots : ℝ) * thresholdRate u t v) := by
  have h := shared_threshold_error_bounds shots u t v hu0 hut htv hv1
    p q hp0 hpu hvq hq1
  have hN : 0 ≤ (shots : ℝ) := Nat.cast_nonneg shots
  have heL : Real.exp (-(shots : ℝ) * bernoulliKL t u) ≤
      Real.exp (-(shots : ℝ) * thresholdRate u t v) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left
      (min_le_left (bernoulliKL t u) (bernoulliKL t v)) hN
    change -(shots : ℝ) * bernoulliKL t u ≤ _
    unfold thresholdRate
    linarith
  have heR : Real.exp (-(shots : ℝ) * bernoulliKL t v) ≤
      Real.exp (-(shots : ℝ) * thresholdRate u t v) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left
      (min_le_right (bernoulliKL t u) (bernoulliKL t v)) hN
    unfold thresholdRate
    linarith
  unfold thresholdRisk
  linarith [h.1, h.2]

/-- One shot budget works for every allowed pair of unknown fixed parameters. -/
theorem uniform_target_error_of_log_budget (shots : ℕ) (u t v eps : ℝ)
    (hu0 : 0 < u) (hut : u < t) (htv : t < v) (hv1 : v < 1)
    (heps : 0 < eps)
    (hbudget : Real.log (1 / eps) ≤ (shots : ℝ) * thresholdRate u t v) :
    ∀ p q : Set.Icc (0 : ℝ) 1,
      0 < (p : ℝ) → (p : ℝ) ≤ u → v ≤ (q : ℝ) → (q : ℝ) < 1 →
      thresholdRisk shots t p q ≤ eps := by
  intro p q hp0 hpu hvq hq1
  have h := threshold_risk_le_exponential shots u t v hu0 hut htv hv1 p q hp0 hpu hvq hq1
  have hexp : Real.exp (-(shots : ℝ) * thresholdRate u t v) ≤ eps := by
    calc
      _ ≤ Real.exp (Real.log eps) := by
        apply Real.exp_le_exp.mpr
        simp only [one_div, Real.log_inv] at hbudget
        linarith
      _ = eps := Real.exp_log heps
  exact h.trans hexp

#print axioms kl_lower_endpoint_bound
#print axioms kl_upper_endpoint_bound
#print axioms exists_one_test_for_all_parameters
#print axioms threshold_rate_pos
#print axioms uniform_target_error_of_log_budget

end
end D5.S3.Estimation.ErrorExponents.BernoulliIntervalThreshold
