/- GID: D5/S3/Estimation/FanoDivergenceForm
   generality: G
   mirror-B: D5/B/S3/Estimation/FanoDivergenceForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive product and quotient hypothesis-counting forms of finite uniform-prior Fano. -/

import D5.S3.Estimation.FanoErrorBound

/-!
# Hypothesis-counting forms of finite Fano

For `p : Y × X → ℝ`, the first coordinate is the observation and the second is the hidden
hypothesis.

The counting form bounds `log (card X)` at a prescribed error level. Its product form has no
`ε < 1` side condition and includes the singleton case. Only the quotient form needs `ε < 1`,
exactly to make division by `1 - ε` order-preserving.
-/

/- Library-search audit trail (2026-08-12):
   * Pinned mathlib searches covered counting/cardinality forms of Fano and the order lemmas used
     to multiply and divide inequalities. No finite Fano hypothesis-counting theorem was found.
     The reusable order facts are `le_div_iff₀` and `Real.log_pos`.
   * The actual working tree under `D5/` was searched for counting/cardinality forms and
     hypothesis-resolution language. No counting form was found.
-/

namespace D5.S3.Estimation.FanoDivergenceForm

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MutualInformation
open D5.S3.Estimation.FanoErrorBound

open Classical in
/-- Side-condition-free counting form of uniform Fano. An arbitrary estimator with error at most
`ε` can resolve only enough hypotheses for `(1 - ε) * log (card X)` to fit in the information
budget. At `ε ≥ 1` the statement remains true but can be vacuous. -/
theorem fano_hypothesis_count_product_bound_uniform
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε) :
    (1 - ε) * Real.log (Fintype.card X) ≤ mutualInformation p + Real.log 2 := by
  letI : Nonempty X := by
    by_contra hX
    letI : IsEmpty X := not_nonempty_iff.mp hX
    simpa using hp.2
  by_cases hcard : Fintype.card X = 1
  · have hrhs : 0 ≤ mutualInformation p + Real.log 2 :=
      add_nonneg (mutual_information_nonneg p hp) (Real.log_pos (by norm_num)).le
    simpa [hcard] using hrhs
  · have hX : 2 ≤ Fintype.card X := by
      have hcard_pos : 0 < Fintype.card X := Fintype.card_pos_iff.mpr inferInstance
      omega
    have hfano := fano_error_probability_lower_bound_uniform p g hp hX huniform
    have hfloor :
        1 - (mutualInformation p + Real.log 2) / Real.log (Fintype.card X) ≤ ε :=
      hfano.trans herror
    have hcard_gt_one : 1 < Fintype.card X := by omega
    have hcard_real_gt_one : (1 : ℝ) < Fintype.card X := by exact_mod_cast hcard_gt_one
    have hlog_pos : 0 < Real.log (Fintype.card X) := Real.log_pos hcard_real_gt_one
    have hratio :
        1 - ε ≤ (mutualInformation p + Real.log 2) / Real.log (Fintype.card X) := by
      linarith
    exact (le_div_iff₀ hlog_pos).1 hratio

open Classical in
/-- Quotient counting form. The sole extra condition `ε < 1` makes `1 - ε` positive, so the
side-condition-free product bound may be divided without reversing the order. -/
theorem fano_hypothesis_count_bound_uniform
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε)
    (hε : ε < 1) :
    Real.log (Fintype.card X) ≤
      (mutualInformation p + Real.log 2) / (1 - ε) := by
  apply (le_div_iff₀ (sub_pos.mpr hε)).2
  simpa [mul_comm] using
    fano_hypothesis_count_product_bound_uniform p g ε hp huniform herror

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε) :
    (1 - ε) * Real.log (Fintype.card X) ≤ mutualInformation p + Real.log 2 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact fano_hypothesis_count_product_bound_uniform p g ε hp huniform herror

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε)
    (hε : ε < 1) :
    Real.log (Fintype.card X) ≤
      (mutualInformation p + Real.log 2) / (1 - ε) := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact fano_hypothesis_count_bound_uniform p g ε hp huniform herror hε

/- Informative counting regime: with zero information and target error `ε = 1/2`, Fano gives
`log M ≤ log 4`, hence at most four hypotheses can be resolved. -/
example (M : ℕ) (hM : 1 ≤ M)
    (hcount :
      Real.log (M : ℝ) ≤
        ((0 : ℝ) + Real.log 2) / (1 - (1 / 2 : ℝ))) :
    M ≤ 4 := by
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog_two_ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hbudget :
      ((0 : ℝ) + Real.log 2) / (1 - (1 / 2 : ℝ)) = Real.log 4 := by
    rw [hlog_four]
    field_simp [hlog_two_ne]
    ring
  have hlog : Real.log (M : ℝ) ≤ Real.log 4 := by
    rwa [hbudget] at hcount
  have hM_pos_nat : 0 < M := by omega
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast hM_pos_nat
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hM_pos, Real.exp_log (by norm_num : (0 : ℝ) < 4)] at hexp
  exact_mod_cast hexp

/- Vacuous counting regime: at target error `ε = 1`, the product form reduces to a nonnegative
information budget and bounds no cardinality; this holds for every `M`. -/
example (M : ℕ) :
    (1 - (1 : ℝ)) * Real.log M ≤ (0 : ℝ) + Real.log 2 := by
  simpa using (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

#print axioms fano_hypothesis_count_product_bound_uniform
#print axioms fano_hypothesis_count_bound_uniform

end D5.S3.Estimation.FanoDivergenceForm
