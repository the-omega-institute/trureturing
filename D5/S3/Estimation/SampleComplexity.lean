/- GID: D5/S3/Estimation/SampleComplexity
   generality: G
   mirror-B: D5/B/S3/Estimation/SampleComplexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Invert n-trial divergence testing floors into a sample-complexity lower bound. -/

/- Library-search audit trail (2026-08-11):
   * Pinned-mathlib declaration searches for the required square-root, exponential, and
     logarithm comparisons found `Real.le_sqrt'`, `Real.log_le_log_iff`, `Real.log_exp`, and
     `Real.log_inv`. These are the monotonicity and rearrangement steps used in the inversion.
   * Declaration-shaped repository searches for `sample` or `complexity` found only the
     unrelated S1 twelve-scale and golden-factor declarations. The Estimation bucket had no
     sample-complexity declaration. The frozen n-fold encoding and bounds below are therefore
     imported and consumed directly.
-/

import D5.S3.Estimation.TestingDivergenceBounds
import D5.S3.DivergenceSupport.PowerAdditivity
import D5.S3.RenyiDivergence.PowerAdditivity

/-!
# Sample-complexity lower bounds

The two n-sample floors are CHAINED COROLLARIES: they only feed the frozen product-law
propagation and KL-additivity results into the corresponding frozen single-trial testing bound.

The inversion uses Bretagnolle--Huber because its floor stays strictly positive at every finite
divergence, while the frozen Pinsker comparison records that its floor is already nonpositive
from divergence two onward. For `0 < ε < 1`, the quantity `2 * ε - ε ^ 2` lies strictly between
zero and one. The result is stated as a lower bound on `n * D`, avoiding the extraneous
hypothesis `D ≠ 0` that division by `D` would require.
-/

namespace D5.S3.Estimation.SampleComplexity

open D5.S3.Divergence.ClassicalDPI
open D5.S3.DivergenceSupport.PowerAdditivity
open D5.S3.Estimation.TestingDivergenceBounds
open D5.S3.RenyiDivergence

open Classical in
/-- CHAINED COROLLARY of the frozen Pinsker testing floor and frozen KL power additivity. -/
theorem iid_testing_error_pinsker {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (A : Finset (IidSpace ι n))
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    1 - Real.sqrt (n * klDivergence p q / 2) ≤
      (∑ z ∈ A, iidPower p n z) + ∑ z ∈ Aᶜ, iidPower q n z := by
  have hac_n :
      ∀ z, iidPower q n z = 0 → iidPower p n z = 0 := by
    intro z hz
    exact ((iid_power_pos q hq n z).ne' hz).elim
  simpa only [kl_divergence_power_additive p q n hp_sum hp hq] using
    testing_error_pinsker (iidPower p n) (iidPower q n) A
      ⟨iid_power_nonneg p (fun i => (hp i).le) n,
        iid_power_sum_one p hp_sum n⟩
      ⟨iid_power_nonneg q (fun i => (hq i).le) n,
        iid_power_sum_one q hq_sum n⟩ hac_n

open Classical in
/-- CHAINED COROLLARY of the frozen Bretagnolle--Huber testing floor and frozen KL power
additivity. -/
theorem iid_testing_error_bretagnolle_huber {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (A : Finset (IidSpace ι n))
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    1 - Real.sqrt (1 - Real.exp (-(n * klDivergence p q))) ≤
      (∑ z ∈ A, iidPower p n z) + ∑ z ∈ Aᶜ, iidPower q n z := by
  have hac_n :
      ∀ z, iidPower q n z = 0 → iidPower p n z = 0 := by
    intro z hz
    exact ((iid_power_pos q hq n z).ne' hz).elim
  simpa only [kl_divergence_power_additive p q n hp_sum hp hq] using
    testing_error_bretagnolle_huber (iidPower p n) (iidPower q n) A
      ⟨iid_power_nonneg p (fun i => (hp i).le) n,
        iid_power_sum_one p hp_sum n⟩
      ⟨iid_power_nonneg q (fun i => (hq i).le) n,
        iid_power_sum_one q hq_sum n⟩ hac_n

open Classical in
/-- Any n-trial test with total error at most `ε`, for `0 < ε < 1`, forces the displayed
sample-complexity lower bound. The `n * D` form avoids a nonzero-divergence side condition. -/
theorem sample_complexity_bretagnolle_huber {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (A : Finset (IidSpace ι n)) (ε : ℝ)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (herror :
      (∑ z ∈ A, iidPower p n z) + ∑ z ∈ Aᶜ, iidPower q n z ≤ ε) :
    Real.log (1 / (2 * ε - ε ^ 2)) ≤ n * klDivergence p q := by
  have hfloor :
      1 - Real.sqrt (1 - Real.exp (-(n * klDivergence p q))) ≤ ε :=
    (iid_testing_error_bretagnolle_huber p q n A hp_sum hq_sum hp hq).trans herror
  have hsqrt :
      1 - ε ≤ Real.sqrt (1 - Real.exp (-(n * klDivergence p q))) := by
    linarith
  have hsquare :
      (1 - ε) ^ 2 ≤ 1 - Real.exp (-(n * klDivergence p q)) :=
    (Real.le_sqrt' (sub_pos.mpr hε_lt_one)).mp hsqrt
  have hexp :
      Real.exp (-(n * klDivergence p q)) ≤ 2 * ε - ε ^ 2 := by
    nlinarith
  have htwo_sub : 0 < 2 - ε := by
    linarith
  have hdenom_pos : 0 < 2 * ε - ε ^ 2 := by
    nlinarith [mul_pos hε_pos htwo_sub]
  have hlog :
      -(n * klDivergence p q) ≤ Real.log (2 * ε - ε ^ 2) := by
    have hlog_exp :=
      (Real.log_le_log_iff (Real.exp_pos _) hdenom_pos).2 hexp
    simpa only [Real.log_exp] using hlog_exp
  rw [one_div, Real.log_inv]
  linarith

open Classical in
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (A : Finset (IidSpace ι n))
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    1 - Real.sqrt (n * klDivergence p q / 2) ≤
      (∑ z ∈ A, iidPower p n z) + ∑ z ∈ Aᶜ, iidPower q n z := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact iid_testing_error_pinsker p q n A hp_sum hq_sum hp hq

open Classical in
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (A : Finset (IidSpace ι n))
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    1 - Real.sqrt (1 - Real.exp (-(n * klDivergence p q))) ≤
      (∑ z ∈ A, iidPower p n z) + ∑ z ∈ Aᶜ, iidPower q n z := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact iid_testing_error_bretagnolle_huber p q n A hp_sum hq_sum hp hq

open Classical in
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (A : Finset (IidSpace ι n)) (ε : ℝ)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (herror :
      (∑ z ∈ A, iidPower p n z) + ∑ z ∈ Aᶜ, iidPower q n z ≤ ε) :
    Real.log (1 / (2 * ε - ε ^ 2)) ≤ n * klDivergence p q := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact sample_complexity_bretagnolle_huber p q n A ε hp_sum hq_sum hp hq
    hε_pos hε_lt_one herror

open Classical in
/-- At error `ε = 1/2` and divergence `D = log (4/3) / 4`, the inversion requires at least
four trials. -/
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (n : Nat) (A : Finset (IidSpace ι n))
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hD : klDivergence p q = Real.log (4 / 3) / 4)
    (herror :
      (∑ z ∈ A, iidPower p n z) + ∑ z ∈ Aᶜ, iidPower q n z ≤ (1 / 2 : ℝ)) :
    (4 : ℝ) ≤ n := by
  have hbound :=
    sample_complexity_bretagnolle_huber p q n A (1 / 2) hp_sum hq_sum hp hq
      (by norm_num) (by norm_num) herror
  have hbound' : Real.log (4 / 3) ≤ n * klDivergence p q := by
    convert hbound using 1
    norm_num
  rw [hD] at hbound'
  have hlog_pos : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have hmul :
      (4 : ℝ) * Real.log (4 / 3) ≤ n * Real.log (4 / 3) := by
    nlinarith
  exact le_of_mul_le_mul_right hmul hlog_pos

#print axioms iid_testing_error_pinsker
#print axioms iid_testing_error_bretagnolle_huber
#print axioms sample_complexity_bretagnolle_huber

end D5.S3.Estimation.SampleComplexity
