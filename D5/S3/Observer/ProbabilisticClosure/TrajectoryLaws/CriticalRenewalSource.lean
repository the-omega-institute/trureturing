/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CriticalRenewalSource
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CriticalRenewalSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact polynomial exponential renewal laws and a common scalar neighborhood. -/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical Filter Finset MeasureTheory
open scoped Topology BigOperators ENNReal

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CriticalRenewalSource

/-- Positive-index power weight; in particular the zeroth moment has no atom at zero. -/
def term (m : ℕ) (s : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else (k : ℝ)^m * Real.exp (-s * k)

def powerSum (m : ℕ) (s : ℝ) : ℝ := ∑' k, term m s k

def weight (r : ℕ) (c : ℝ) (i : Bool) (s : ℝ) (k : ℕ) : ℝ :=
  term (2*r-1) s k + if i then c * term (r-1) s k else 0

def normalizer (r : ℕ) (c : ℝ) (i : Bool) (s : ℝ) : ℝ :=
  ∑' k, weight r c i s k

def density (r : ℕ) (c : ℝ) (i : Bool) (s : ℝ) (k : ℕ) : ℝ :=
  weight r c i s k / normalizer r c i s

def moment (r : ℕ) (c : ℝ) (i : Bool) (s : ℝ) (p : ℕ) : ℝ :=
  ∑' k, (k : ℝ)^p * density r c i s k

def mean (r : ℕ) (c : ℝ) (i : Bool) (s : ℝ) : ℝ :=
  moment r c i s 1 + 1

def beta (r : ℕ) (c : ℝ) (i : Bool) (s : ℝ) : ℝ :=
  (moment r c i s 2 + moment r c i s 1) / (2 * mean r c i s)

def tail (r : ℕ) (c : ℝ) (i : Bool) (s : ℝ) (u : ℕ) : ℝ :=
  ∑' k, if u ≤ k then density r c i s k else 0

def equilibrium (r : ℕ) (c : ℝ) (i : Bool) (s : ℝ) (u : ℕ) : ℝ :=
  tail r c i s u / mean r c i s

def quotient (r : ℕ) (s : ℝ) : ℝ := powerSum (r-1) s / powerSum (2*r-1) s

private lemma exp_norm_lt_one {s : ℝ} (hs : 0 < s) :
    ‖Real.exp (-s)‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (Real.exp_lt_one_iff).2 (by linarith)

private lemma exp_natural (s : ℝ) (k : ℕ) :
    Real.exp (-s * k) = Real.exp (-s)^k := by
  simpa using Real.exp_nat_mul (-s) k

private lemma summable_term (m : ℕ) {s : ℝ} (hs : 0 < s) :
    Summable (term m s) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one m (exp_norm_lt_one hs)
  have he : term m s = fun k : ℕ =>
      (k : ℝ)^m * Real.exp (-s)^k - if k = 0 then (0 : ℝ)^m else 0 := by
    funext k
    by_cases hk : k = 0 <;> simp [term, hk, exp_natural]
  rw [he]
  exact h.sub (summable_ite_eq 0 _)

private lemma term_nonneg (m : ℕ) (s : ℝ) (k : ℕ) : 0 ≤ term m s k := by
  unfold term
  split_ifs <;> positivity

private lemma powerSum_pos (m : ℕ) {s : ℝ} (hs : 0 < s) : 0 < powerSum m s := by
  exact (summable_term m hs).tsum_pos (term_nonneg m s) 1 (by simp [term]; positivity)

private lemma weighted_term (p m : ℕ) (s : ℝ) (k : ℕ) :
    (k : ℝ)^p * term m s k = term (m+p) s k := by
  by_cases hk : k = 0 <;> simp [term, hk, pow_add] <;> ring

private lemma summable_weighted (r p : ℕ) (c : ℝ) (i : Bool)
    {s : ℝ} (hs : 0 < s) :
    Summable (fun k => (k : ℝ)^p * weight r c i s k) := by
  cases i
  · simpa [weight, weighted_term] using summable_term (2*r-1+p) hs
  · have h := (summable_term (2*r-1+p) hs).add
      ((summable_term (r-1+p) hs).mul_left c)
    convert h using 1
    funext k
    simp only [weight, Bool.true_eq, ↓reduceIte, mul_add]
    rw [← weighted_term, ← weighted_term]
    ring

private lemma summable_weight (r : ℕ) (c : ℝ) (i : Bool)
    {s : ℝ} (hs : 0 < s) : Summable (weight r c i s) := by
  simpa using summable_weighted r 0 c i hs

private lemma weight_nonneg (r : ℕ) {c : ℝ} (hc : 0 < c) (i : Bool)
    (s : ℝ) (k : ℕ) : 0 ≤ weight r c i s k := by
  cases i <;> simp only [weight, Bool.false_eq_true, ↓reduceIte, add_zero]
  · exact term_nonneg _ _ _
  · exact add_nonneg (term_nonneg _ _ _) (mul_nonneg hc.le (term_nonneg _ _ _))

private lemma normalizer_pos (r : ℕ) {c s : ℝ} (hc : 0 < c)
    (i : Bool) (hs : 0 < s) : 0 < normalizer r c i s := by
  apply (summable_weight r c i hs).tsum_pos (weight_nonneg r hc i s) 1
  cases i <;> simp [weight, term] <;> positivity

private lemma normalizer_eq (r : ℕ) (c : ℝ) (i : Bool)
    {s : ℝ} (hs : 0 < s) :
    normalizer r c i s = powerSum (2*r-1) s + if i then c*powerSum (r-1) s else 0 := by
  cases i
  · simp [normalizer, weight, powerSum]
  · simp only [normalizer, weight, ↓reduceIte]
    rw [Summable.tsum_add (summable_term _ hs) ((summable_term _ hs).mul_left c),
      tsum_mul_left]
    rfl

private lemma summable_density_moment (r p : ℕ) (c : ℝ) (i : Bool)
    {s : ℝ} (hs : 0 < s) :
    Summable (fun k => (k : ℝ)^p * density r c i s k) := by
  simpa [density, mul_div_assoc] using
    (summable_weighted r p c i hs).div_const (normalizer r c i s)

private lemma density_nonneg (r : ℕ) {c s : ℝ} (hc : 0 < c)
    (i : Bool) (hs : 0 < s) (k : ℕ) : 0 ≤ density r c i s k :=
  div_nonneg (weight_nonneg r hc i s k) (normalizer_pos r hc i hs).le

private lemma density_sum (r : ℕ) {c s : ℝ} (hc : 0 < c)
    (i : Bool) (hs : 0 < s) : ∑' k, density r c i s k = 1 := by
  simp only [density, tsum_div_const]
  exact div_self (normalizer_pos r hc i hs).ne'

private lemma moment_eq (r p : ℕ) (c : ℝ) (i : Bool)
    {s : ℝ} (hs : 0 < s) :
    moment r c i s p =
      (powerSum (2*r-1+p) s + if i then c*powerSum (r-1+p) s else 0) /
        normalizer r c i s := by
  unfold moment density
  simp_rw [mul_div_assoc]
  rw [tsum_div_const]
  congr 1
  cases i
  · simp [weight, weighted_term, powerSum]
  · simp only [weight, ↓reduceIte, mul_add]
    simp_rw [mul_left_comm (· : ℝ), weighted_term]
    rw [Summable.tsum_add (summable_term _ hs) ((summable_term _ hs).mul_left c),
      tsum_mul_left]
    rfl

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CriticalRenewalSource
