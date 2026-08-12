/- GID: D5/S3/Estimation/FanoMethodSampleComplexity
   generality: I
   mirror-B: D5/B/S3/Estimation/FanoMethodSampleComplexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive finite-family sample complexity from Fano and KL power additivity. -/

import D5.S3.Estimation.FanoMethod
import D5.S3.DivergenceSupport.PowerAdditivity
import D5.S3.RenyiDivergence.PowerAdditivity

/-!
# Finite-family sample complexity

These bounds are chiefly compositions. The averaging equality and the one-sample Fano method are
frozen in `FanoMethod`, while exact linear growth of KL under independent repetition is frozen in
`DivergenceSupport.PowerAdditivity`. The only new proof obligations are propagation of strict
positivity and normalization to the product laws, followed by the order-theoretic inversion of the
product bound.

The product form has no sign assumption on the divergence ceiling. Solving for the sample count
requires `0 < D`, exactly because division must preserve order. At `D = 0`, Gibbs nonnegativity and
equality, together with the standing strict positivity and normalization hypotheses, force every
candidate law to equal the reference law. Hence all labels induce the same observations, and no
finite repetition can distinguish them at a genuinely discriminating error target.
-/

/- Library-search audit trail (2026-08-12):
   * Pinned mathlib was searched for sample-complexity, minimax-rate, Fano-method, multiple-
     hypothesis, and hypothesis-testing declarations. No matching finite-family sample-complexity
     theorem was found. The inversion reuses `div_le_iff₀`; arithmetic normalization uses existing
     logarithm identities and the certified bounds `Real.log_two_gt_d9`, `Real.log_two_lt_d9`, and
     `Real.log_five_gt_d9`.
   * The working tree under `D5/` was independently searched for n-fold mixtures, family sample
     complexity, Fano with repeated observations, and declarations combining `iidPower` with a
     mixture. The only sample-complexity result found was the two-candidate
     `Estimation.SampleComplexity`; no n-fold family mixture or requested family theorem was found.
-/

namespace D5.S3.Estimation.FanoMethodSampleComplexity

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.ChainRule
open D5.S3.DivergenceSupport.PowerAdditivity
open D5.S3.Entropy.MutualInformation
open D5.S3.Estimation.FanoMethod
open D5.S3.Estimation.FanoReferenceDivergence
open D5.S3.RenyiDivergence

open Classical in
/-- Mutual information in an `n`-sample uniform family is at most `n` times the average
single-observation divergence to a common reference. -/
theorem mutual_information_iid_le_average_reference_divergence
    {ι X : Type*} [Fintype ι] [Fintype X]
    (n : Nat) (p : IidSpace ι n × X → ℝ) (P : X → ι → ℝ) (Q : ι → ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i x, 0 < P i x) (hP_sum : ∀ i, ∑ x, P i x = 1)
    (hQ : ∀ x, 0 < Q x) (hQ_sum : ∑ x, Q x = 1)
    (hmix : ∀ z : IidSpace ι n × X,
      p z = (Fintype.card X : ℝ)⁻¹ * iidPower (P z.2) n z.1) :
    mutualInformation p ≤
      (n : ℝ) * ((Fintype.card X : ℝ)⁻¹ * ∑ i, klDivergence (P i) Q) := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  classical
  have hP_power :
      ∀ i, (∀ z, 0 ≤ iidPower (P i) n z) ∧ ∑ z, iidPower (P i) n z = 1 :=
    fun i =>
      ⟨iid_power_nonneg (P i) (fun x => (hP i x).le) n,
        iid_power_sum_one (P i) (hP_sum i) n⟩
  calc
    mutualInformation p ≤
        klDivergence p
          (fun z => iidPower Q n z.1 *
            marginal (fun r : X × IidSpace ι n => p (r.2, r.1)) z.2) :=
      mutual_information_le_product_reference_divergence
        p (iidPower Q n) hp (iid_power_pos Q hQ n)
          (iid_power_sum_one Q hQ_sum n)
    _ =
        (Fintype.card X : ℝ)⁻¹ *
          ∑ i, klDivergence (iidPower (P i) n) (iidPower Q n) :=
      kl_divergence_uniform_mixture_eq_average
        p (fun i => iidPower (P i) n) (iidPower Q n) hp hP_power
          (iid_power_pos Q hQ n) (iid_power_sum_one Q hQ_sum n) hmix
    _ = (Fintype.card X : ℝ)⁻¹ *
          ∑ i, (n : ℝ) * klDivergence (P i) Q := by
      apply congrArg (fun t : ℝ => (Fintype.card X : ℝ)⁻¹ * t)
      apply Finset.sum_congr rfl
      intro i _
      exact kl_divergence_power_additive (P i) Q n (hP_sum i) (hP i) hQ
    _ = (n : ℝ) *
          ((Fintype.card X : ℝ)⁻¹ * ∑ i, klDivergence (P i) Q) := by
      rw [← Finset.mul_sum]
      ring

open Classical in
/-- If every one-sample candidate divergence is at most `D`, then `n` samples carry at most
`n * D` mutual information. -/
theorem mutual_information_iid_le_uniform_reference_divergence
    {ι X : Type*} [Fintype ι] [Fintype X]
    (n : Nat) (p : IidSpace ι n × X → ℝ) (P : X → ι → ℝ) (Q : ι → ℝ)
    (D : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i x, 0 < P i x) (hP_sum : ∀ i, ∑ x, P i x = 1)
    (hQ : ∀ x, 0 < Q x) (hQ_sum : ∑ x, Q x = 1)
    (hmix : ∀ z : IidSpace ι n × X,
      p z = (Fintype.card X : ℝ)⁻¹ * iidPower (P z.2) n z.1)
    (hdiv : ∀ i, klDivergence (P i) Q ≤ D) :
    mutualInformation p ≤ (n : ℝ) * D := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  classical
  have hP_power :
      ∀ i, (∀ z, 0 ≤ iidPower (P i) n z) ∧ ∑ z, iidPower (P i) n z = 1 :=
    fun i =>
      ⟨iid_power_nonneg (P i) (fun x => (hP i x).le) n,
        iid_power_sum_one (P i) (hP_sum i) n⟩
  have hdiv_power :
      ∀ i, klDivergence (iidPower (P i) n) (iidPower Q n) ≤ (n : ℝ) * D := by
    intro i
    rw [kl_divergence_power_additive (P i) Q n (hP_sum i) (hP i) hQ]
    exact mul_le_mul_of_nonneg_left (hdiv i) (Nat.cast_nonneg n)
  exact
    mutual_information_le_uniform_reference_divergence
      p (fun i => iidPower (P i) n) (iidPower Q n) ((n : ℝ) * D)
      hp hP_power (iid_power_pos Q hQ n) (iid_power_sum_one Q hQ_sum n)
      hmix hdiv_power

open Classical in
/-- Fano's method for an arbitrary estimator on `n` independent observations, in the primary
product form with no sign side condition on `D`. -/
theorem fano_method_iid_minimax_product_bound
    {ι X : Type*} [Fintype ι] [Fintype X]
    (n : Nat) (p : IidSpace ι n × X → ℝ) (P : X → ι → ℝ) (Q : ι → ℝ)
    (g : IidSpace ι n → X) (D ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i x, 0 < P i x) (hP_sum : ∀ i, ∑ x, P i x = 1)
    (hQ : ∀ x, 0 < Q x) (hQ_sum : ∑ x, Q x = 1)
    (hmix : ∀ z : IidSpace ι n × X,
      p z = (Fintype.card X : ℝ)⁻¹ * iidPower (P z.2) n z.1)
    (hdiv : ∀ i, klDivergence (P i) Q ≤ D)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε) :
    (1 - ε) * Real.log (Fintype.card X) ≤ (n : ℝ) * D + Real.log 2 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  classical
  have hP_power :
      ∀ i, (∀ z, 0 ≤ iidPower (P i) n z) ∧ ∑ z, iidPower (P i) n z = 1 :=
    fun i =>
      ⟨iid_power_nonneg (P i) (fun x => (hP i x).le) n,
        iid_power_sum_one (P i) (hP_sum i) n⟩
  have hdiv_power :
      ∀ i, klDivergence (iidPower (P i) n) (iidPower Q n) ≤ (n : ℝ) * D := by
    intro i
    rw [kl_divergence_power_additive (P i) Q n (hP_sum i) (hP i) hQ]
    exact mul_le_mul_of_nonneg_left (hdiv i) (Nat.cast_nonneg n)
  exact
    fano_method_minimax_product_bound
      p (fun i => iidPower (P i) n) (iidPower Q n) g ((n : ℝ) * D) ε
      hp hP_power (iid_power_pos Q hQ n) (iid_power_sum_one Q hQ_sum n)
      hmix hdiv_power herror

open Classical in
/-- Solved sample-complexity form. Positivity of `D` is precisely the side condition required
to divide the product bound without reversing its order. -/
theorem fano_method_iid_sample_complexity_lower_bound
    {ι X : Type*} [Fintype ι] [Fintype X]
    (n : Nat) (p : IidSpace ι n × X → ℝ) (P : X → ι → ℝ) (Q : ι → ℝ)
    (g : IidSpace ι n → X) (D ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i x, 0 < P i x) (hP_sum : ∀ i, ∑ x, P i x = 1)
    (hQ : ∀ x, 0 < Q x) (hQ_sum : ∑ x, Q x = 1)
    (hmix : ∀ z : IidSpace ι n × X,
      p z = (Fintype.card X : ℝ)⁻¹ * iidPower (P z.2) n z.1)
    (hdiv : ∀ i, klDivergence (P i) Q ≤ D)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε)
    (hD : 0 < D) :
    ((1 - ε) * Real.log (Fintype.card X) - Real.log 2) / D ≤ (n : ℝ) := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hproduct :=
    fano_method_iid_minimax_product_bound
      n p P Q g D ε hp hP hP_sum hQ hQ_sum hmix hdiv herror
  apply (div_le_iff₀ hD).2
  linarith

open Classical in
/-- With 1000 candidates, error at most one percent, and one-sample divergence at most `0.1`,
every estimator needs more than `61.455` observations and hence at least 62 observations. -/
theorem fano_method_thousand_candidates_one_percent
    {ι X : Type*} [Fintype ι] [Fintype X]
    (n : Nat) (p : IidSpace ι n × X → ℝ) (P : X → ι → ℝ) (Q : ι → ℝ)
    (g : IidSpace ι n → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i x, 0 < P i x) (hP_sum : ∀ i, ∑ x, P i x = 1)
    (hQ : ∀ x, 0 < Q x) (hQ_sum : ∑ x, Q x = 1)
    (hmix : ∀ z : IidSpace ι n × X,
      p z = (Fintype.card X : ℝ)⁻¹ * iidPower (P z.2) n z.1)
    (hcard : Fintype.card X = 1000)
    (hdiv : ∀ i, klDivergence (P i) Q ≤ (1 / 10 : ℝ))
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ (1 / 100 : ℝ)) :
    (61.455 : ℝ) < (n : ℝ) ∧ 62 ≤ n := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hproduct :=
    fano_method_iid_minimax_product_bound
      n p P Q g (1 / 10 : ℝ) (1 / 100 : ℝ)
      hp hP hP_sum hQ hQ_sum hmix hdiv herror
  rw [hcard] at hproduct
  have hlog_thousand :
      Real.log (1000 : ℝ) = 3 * (Real.log 2 + Real.log 5) := by
    rw [show (1000 : ℝ) = (2 * 5) ^ 3 by norm_num, Real.log_pow,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
    norm_num
  norm_num at hproduct
  rw [hlog_thousand] at hproduct
  have hn_real : (61.455 : ℝ) < (n : ℝ) := by
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_five_gt_d9]
  refine ⟨hn_real, ?_⟩
  have hn_real' : (61 : ℝ) < (n : ℝ) := by linarith
  have hn_nat : 61 < n := by exact_mod_cast hn_real'
  omega

/-- At four candidates and unit tolerated error, the numerator is negative. The product bound
already holds at zero samples and the solved lower floor is strictly below zero, so the sample-
complexity statement must be vacuous in this regime. -/
theorem fano_method_four_candidates_unit_error_vacuous :
    (1 - (1 : ℝ)) * Real.log 4 ≤
        (0 : ℝ) * (1 / 10 : ℝ) + Real.log 2 ∧
      ((1 - (1 : ℝ)) * Real.log 4 - Real.log 2) / (1 / 10 : ℝ) < 0 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · norm_num
    exact hlog_two_pos.le
  · norm_num
    linarith

#print axioms mutual_information_iid_le_average_reference_divergence
#print axioms mutual_information_iid_le_uniform_reference_divergence
#print axioms fano_method_iid_minimax_product_bound
#print axioms fano_method_iid_sample_complexity_lower_bound
#print axioms fano_method_thousand_candidates_one_percent
#print axioms fano_method_four_candidates_unit_error_vacuous

end D5.S3.Estimation.FanoMethodSampleComplexity
