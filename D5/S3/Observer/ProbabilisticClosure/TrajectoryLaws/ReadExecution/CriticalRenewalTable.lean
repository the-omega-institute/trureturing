/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact renewal source laws and literal counted rows with their complete-gap law. -/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.GeometricPhaseOccupation
import Mathlib.Data.Int.Interval

section
/-!
# Exact critical renewal sources

Polynomial exponential gap densities have an equilibrium forward-wait distribution.
Finite Stirling formulas give a common scalar neighborhood for both labels.
-/

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
  ∑' k : ℕ, (k : ℝ)^p * density r c i s k

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
  simpa [mul_comm] using Real.exp_nat_mul (-s) k

private lemma summable_term (m : ℕ) {s : ℝ} (hs : 0 < s) :
    Summable (term m s) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one m (exp_norm_lt_one hs)
  have he : term m s = fun k : ℕ =>
      (k : ℝ)^m * Real.exp (-s)^k - if k = 0 then (0 : ℝ)^m else 0 := by
    funext k
    by_cases hk : k = 0 <;> simp only [term, hk, ↓reduceIte, exp_natural, sub_zero, Nat.cast_zero, mul_zero, Real.exp_zero, pow_zero, mul_one, sub_self]
  rw [he]
  exact h.sub (summable_of_ne_finset_zero (s := {0}) (by intro b hb; simp only [mem_singleton] at hb; simp [hb]))

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
    Summable (fun k : ℕ => (k : ℝ)^p * weight r c i s k) := by
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
    Summable (fun k : ℕ => (k : ℝ)^p * density r c i s k) := by
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
  simp_rw [← mul_div_assoc]
  rw [tsum_div_const]
  congr 1
  cases i
  · simp [weight, weighted_term, powerSum]
  · simp only [weight, ↓reduceIte, mul_add]
    simp_rw [← mul_assoc, mul_comm _ c, mul_assoc c, weighted_term]
    rw [Summable.tsum_add (summable_term _ hs) ((summable_term _ hs).mul_left c),
      tsum_mul_left]
    rfl

private lemma finite_weight_row (a : ℕ → ℝ) (p k : ℕ) :
    (∑' u : ℕ, if u ≤ k then (u : ℝ)^p * a k else 0) =
      (∑ u ∈ range (k+1), (u : ℝ)^p) * a k := by
  rw [tsum_eq_sum (s := range (k+1)) (fun u hu => by
    have h : ¬u ≤ k := by simpa only [mem_range, Nat.lt_succ_iff] using hu
    simp [h])]
  rw [sum_mul]
  apply sum_congr rfl
  intro u hu
  simp only [mem_range, Nat.lt_succ_iff] at hu
  simp [hu]

private lemma weighted_tails (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (p : ℕ)
    (h : Summable fun k => (∑ u ∈ range (k+1), (u : ℝ)^p) * a k) :
    Summable (fun u : ℕ => (u : ℝ)^p * ∑' k, if u ≤ k then a k else 0) ∧
    (∑' u : ℕ, (u : ℝ)^p * ∑' k, if u ≤ k then a k else 0) =
      ∑' k, (∑ u ∈ range (k+1), (u : ℝ)^p) * a k := by
  let f : ℕ → ℕ → ℝ := fun k u => if u ≤ k then (u : ℝ)^p * a k else 0
  have hn (k u : ℕ) : 0 ≤ f k u := by
    dsimp [f]
    split_ifs
    · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (ha k)
    · exact le_rfl
  have hj : Summable (Function.uncurry f) := by
    apply (summable_prod_of_nonneg (fun z => hn z.1 z.2)).2
    constructor
    · intro k
      apply summable_of_ne_finset_zero (s := range (k+1))
      intro u hu
      have hn : ¬u ≤ k := by simpa only [mem_range, Nat.lt_succ_iff] using hu
      simp [f, hn]
    · simpa only [f, finite_weight_row] using h
  have he : (fun u : ℕ => (u : ℝ)^p * ∑' k, if u ≤ k then a k else 0) =
      fun u => ∑' k, f k u := by
    funext u
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    simp only [f]
    split_ifs <;> simp
  rw [he]
  constructor
  · exact ((summable_prod_of_nonneg (f := fun z : ℕ × ℕ => f z.2 z.1)
      (fun z => hn z.2 z.1)).1 hj.prod_symm).2
  · rw [Summable.tsum_comm (f := f) hj]
    simp only [f, finite_weight_row]

private lemma sum_real_range (k : ℕ) :
    (∑ u ∈ range (k+1), (u : ℝ)) = (k : ℝ)*(k+1)/2 := by
  have h := Finset.sum_range_id_mul_two (k + 1)
  rw [Nat.add_sub_cancel] at h
  have hreal := congrArg (fun n : ℕ => (n : ℝ)) h
  push_cast at hreal
  linarith

private lemma density_summable (r : ℕ) (c : ℝ) (i : Bool) {s : ℝ}
    (hs : 0 < s) : Summable (density r c i s) := by
  simpa using summable_density_moment r 0 c i hs

private lemma tail_mass (r : ℕ) {c s : ℝ} (hc : 0 < c) (i : Bool)
    (hs : 0 < s) :
    Summable (tail r c i s) ∧
      (∑' u, tail r c i s u) = mean r c i s := by
  have h : Summable fun k : ℕ => ((k : ℝ)+1)*density r c i s k := by
    simpa [add_mul, pow_one] using
      (summable_density_moment r 1 c i hs).add (density_summable r c i hs)
  have he := weighted_tails (density r c i s) (density_nonneg r hc i hs) 0
    (by simpa using h)
  simp only [pow_zero, sum_const, card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, mul_one, one_mul] at he
  refine ⟨he.1, ?_⟩
  change (∑' u : ℕ, ∑' k, if u ≤ k then density r c i s k else 0) = _
  rw [he.2]
  simp_rw [add_mul, one_mul]
  rw [Summable.tsum_add (by simpa using summable_density_moment r 1 c i hs)
    (density_summable r c i hs), density_sum r hc i hs]
  simp only [mean, moment, pow_one]

private lemma tail_first_moment (r : ℕ) {c s : ℝ} (hc : 0 < c) (i : Bool)
    (hs : 0 < s) :
    (∑' u : ℕ, (u : ℝ)*tail r c i s u) =
      (moment r c i s 2 + moment r c i s 1)/2 := by
  have h : Summable fun k : ℕ => ((k : ℝ)*(k+1)/2)*density r c i s k := by
    convert ((summable_density_moment r 2 c i hs).add
      (summable_density_moment r 1 c i hs)).div_const 2 using 1
    funext k
    ring
  have he := weighted_tails (density r c i s) (density_nonneg r hc i hs) 1
    (by simpa only [pow_one, sum_real_range] using h)
  simp only [pow_one, sum_real_range] at he
  change (∑' u : ℕ, (u : ℝ) * ∑' k, if u ≤ k then density r c i s k else 0) = _
  rw [he.2]
  calc
    _ = ∑' k : ℕ, ((k : ℝ)^2*density r c i s k +
        (k : ℝ)^1*density r c i s k)/2 := by
      apply tsum_congr
      intro k
      ring
    _ = _ := by
      rw [tsum_div_const, Summable.tsum_add (summable_density_moment r 2 c i hs)
        (summable_density_moment r 1 c i hs)]
      rfl

/-- The finite Stirling numerator after clearing the common geometric denominator. -/
private def stirlingPolynomial (m : ℕ) (q : ℝ) : ℝ :=
  ∑ j ∈ range (m+1), (Nat.stirlingSecond m j : ℝ) * j.factorial *
    q^j * (1-q)^(m-j)

private lemma geometric_numerator (m : ℕ) {s : ℝ} (hs : 0 < s) :
    (1-Real.exp (-s))^(m+1) * (powerSum m s + (0:ℝ)^m) =
      stirlingPolynomial m (Real.exp (-s)) := by
  have hq : 1-Real.exp (-s) ≠ 0 := by
    have := exp_norm_lt_one hs
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at this
    linarith
  have hsum : powerSum m s + (0:ℝ)^m =
      ∑' k : ℕ, (k : ℝ)^m * Real.exp (-s)^k := by
    have he : term m s = fun k : ℕ =>
        (k : ℝ)^m * Real.exp (-s)^k - if k = 0 then (0:ℝ)^m else 0 := by
      funext k
      by_cases hk : k = 0
      · simp [hk, term]
      · simp only [term, hk, ↓reduceIte, exp_natural, sub_zero]
    have hg : Summable (fun k : ℕ => (k : ℝ)^m * Real.exp (-s)^k) :=
      summable_pow_mul_geometric_of_norm_lt_one m (exp_norm_lt_one hs)
    have hsingle : Summable (fun k : ℕ => if k = 0 then (0:ℝ)^m else 0) :=
      summable_of_ne_finset_zero (s := {0}) (by
        intro k hk
        simp only [mem_singleton] at hk
        simp [hk])
    unfold powerSum
    rw [he, hg.tsum_sub hsingle]
    simp
  rw [hsum, tsum_pow_mul_geometric_of_norm_lt_one m (exp_norm_lt_one hs),
    mul_sum]
  unfold stirlingPolynomial
  apply sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (mem_range.1 hj)
  have hp : m+1 = (m-j)+(j+1) := by omega
  rw [hp, pow_add]
  field_simp [hq]
  <;> ring

private lemma stirling_at_one (m : ℕ) :
    stirlingPolynomial m 1 = (m.factorial : ℝ) := by
  unfold stirlingPolynomial
  rw [sum_eq_single m]
  · simp [Nat.stirlingSecond_self]
  · intro j hj hne
    have hmj : m-j ≠ 0 := by
      have := mem_range.1 hj
      omega
    simp [hmj]
  · simp

private lemma scaled_powerSum_limit (m : ℕ) :
    Tendsto (fun s : ℝ => s^(m+1) * powerSum m s) (𝓝[>] 0)
      (𝓝 (m.factorial : ℝ)) := by
  have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hq : Tendsto (fun s : ℝ => Real.exp (-s)) (𝓝[>] 0) (𝓝 1) := by
    simpa using hid.neg.rexp
  have hd : HasDerivAt (fun s : ℝ => 1-Real.exp (-s)) 1 0 := by
    convert (((Real.hasDerivAt_exp (-(0:ℝ))).comp 0
      (hasDerivAt_id (0:ℝ)).neg).const_sub 1) using 1 <;> norm_num
  have hr : Tendsto (fun s : ℝ => s/(1-Real.exp (-s))) (𝓝[>] 0) (𝓝 1) := by
    have ht : Tendsto (fun s : ℝ => (1-Real.exp (-s))/s) (𝓝[>] 0) (𝓝 1) := by
      simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right
    simpa using ht.inv₀ (by norm_num : (1:ℝ) ≠ 0)
  have hc : Continuous (stirlingPolynomial m) := by
    unfold stirlingPolynomial
    fun_prop
  have hp : Tendsto (fun s : ℝ => stirlingPolynomial m (Real.exp (-s)))
      (𝓝[>] 0) (𝓝 (m.factorial : ℝ)) := by
    simpa only [stirling_at_one, Function.comp_def] using hc.continuousAt.tendsto.comp hq
  have hz : Tendsto (fun s : ℝ => (1-Real.exp (-s))^(m+1)*(0:ℝ)^m)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[>] 0) (𝓝 1)).sub hq).pow (m+1)).mul_const ((0:ℝ)^m)
  have hn : Tendsto (fun s : ℝ => (1-Real.exp (-s))^(m+1)*powerSum m s)
      (𝓝[>] 0) (𝓝 (m.factorial : ℝ)) := by
    have hh := hp.sub hz
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [← geometric_numerator m hs]
    ring
  have h := (hr.pow (m+1)).mul hn
  simp only [one_pow, one_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 0 < s at hs
  have hqne : 1-Real.exp (-s) ≠ 0 := by
    have hlt : Real.exp (-s) < 1 := (Real.exp_lt_one_iff).2 (by linarith)
    linarith
  rw [div_pow]
  field_simp [hqne]

/-- Discrete-law facts on the original zero-gap and forward-wait coordinates. -/
structure SourceLaw (r : ℕ) (c : ℝ) (i : Bool) (s : ℝ) : Prop where
  normalizer_positive : 0 < normalizer r c i s
  density_zero : density r c i s 0 = 0
  density_positive : ∀ k : ℕ, 0 < k → 0 < density r c i s k
  density_formula : ∀ k : ℕ, 0 < k →
    density r c i s k =
      ((k : ℝ)^(2*r-1) + if i then c*(k : ℝ)^(r-1) else 0) *
        Real.exp (-s*k) / normalizer r c i s
  density_nonnegative : ∀ k, 0 ≤ density r c i s k
  mass_one : ∑' k, density r c i s k = 1
  finite_moments : ∀ p, Summable (fun k : ℕ => (k : ℝ)^p*density r c i s k)
  mean_positive : 0 < mean r c i s
  cycle_mean : (∑' k : ℕ, ((k : ℝ)+1)*density r c i s k) = mean r c i s
  beta_formula : beta r c i s =
    (∑' k : ℕ, (k : ℝ)*(k+1)*density r c i s k)/(2*mean r c i s)
  tail_zero : tail r c i s 0 = 1
  tail_one : tail r c i s 1 = 1
  tail_summable : Summable (tail r c i s)
  tail_sum : (∑' u, tail r c i s u) = mean r c i s
  wait_nonnegative : ∀ u, 0 ≤ equilibrium r c i s u
  wait_mass_one : (∑' u, equilibrium r c i s u) = 1
  wait_first_summable : Summable (fun u : ℕ => (u : ℝ)*equilibrium r c i s u)
  wait_mean : (∑' u : ℕ, (u : ℝ)*equilibrium r c i s u) = beta r c i s

/-- Exact source laws, including the signed normalizer correction. -/
private lemma source_laws_core (r : ℕ) (_hr : 1 ≤ r) (c : ℝ) (hc : 0 < c)
    (s : ℝ) (hs : 0 < s) :
    (∀ i, SourceLaw r c i s) ∧
    normalizer r c true s = (1+c*quotient r s)*normalizer r c false s ∧
    ∀ k : ℕ, 0 < k →
      density r c true s k-density r c false s k =
        c*((k : ℝ)^(r-1)-quotient r s*(k : ℝ)^(2*r-1))*
          Real.exp (-s*k)/normalizer r c true s := by
  have hzero (i : Bool) : density r c i s 0 = 0 := by
    cases i <;> simp [density, weight, term]
  have hmu (i : Bool) : 0 < mean r c i s := by
    have hn : 0 ≤ moment r c i s 1 := by
      apply tsum_nonneg
      intro k
      exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (density_nonneg r hc i hs k)
    dsimp [mean]
    linarith
  constructor
  · intro i
    have htm := tail_mass r hc i hs
    have hfirst : Summable (fun u : ℕ => (u : ℝ)*tail r c i s u) := by
      have h : Summable (fun k : ℕ =>
          ((k : ℝ)*(k+1)/2)*density r c i s k) := by
        convert ((summable_density_moment r 2 c i hs).add
          (summable_density_moment r 1 c i hs)).div_const 2 using 1
        funext k
        ring
      simpa only [pow_one, sum_real_range, tail] using
        (weighted_tails (density r c i s) (density_nonneg r hc i hs) 1
          (by simpa only [pow_one, sum_real_range] using h)).1
    have htri : (∑' k : ℕ, (k : ℝ)*(k+1)*density r c i s k) =
        moment r c i s 2 + moment r c i s 1 := by
      calc
        _ = ∑' k : ℕ, ((k : ℝ)^2*density r c i s k +
            (k : ℝ)^1*density r c i s k) := by
          apply tsum_congr
          intro k
          ring
        _ = _ := by
          rw [Summable.tsum_add (summable_density_moment r 2 c i hs)
            (summable_density_moment r 1 c i hs)]
          rfl
    refine {
      normalizer_positive := normalizer_pos r hc i hs
      density_zero := hzero i
      density_positive := ?_
      density_formula := ?_
      density_nonnegative := density_nonneg r hc i hs
      mass_one := density_sum r hc i hs
      finite_moments := fun p => summable_density_moment r p c i hs
      mean_positive := hmu i
      cycle_mean := ?_
      beta_formula := ?_
      tail_zero := ?_
      tail_one := ?_
      tail_summable := htm.1
      tail_sum := htm.2
      wait_nonnegative := ?_
      wait_mass_one := ?_
      wait_first_summable := ?_
      wait_mean := ?_
    }
    · intro k hk
      apply div_pos _ (normalizer_pos r hc i hs)
      have ht : 0 < term (2*r-1) s k := by
        simp only [term, hk.ne', ↓reduceIte]
        exact mul_pos (pow_pos (Nat.cast_pos.2 hk) _) (Real.exp_pos _)
      cases i
      · simpa [weight] using ht
      · exact add_pos_of_pos_of_nonneg ht (mul_nonneg hc.le (term_nonneg _ _ _))
    · intro k hk
      cases i <;> simp [density, weight, term, hk.ne', add_mul, mul_assoc]
    · calc
        _ = (∑' k : ℕ, (k : ℝ)*density r c i s k) +
            ∑' k, density r c i s k := by
          simp_rw [add_mul, one_mul]
          rw [Summable.tsum_add (by simpa using summable_density_moment r 1 c i hs)
            (density_summable r c i hs)]
        _ = _ := by simp only [density_sum r hc i hs, mean, moment, pow_one]
    · rw [htri]
      rfl
    · simpa only [tail, Nat.zero_le, ↓reduceIte] using density_sum r hc i hs
    · calc
        _ = ∑' k, density r c i s k := by
          apply tsum_congr
          intro k
          cases k with
          | zero => simp [hzero, tail]
          | succ k => simp [tail]
        _ = 1 := density_sum r hc i hs
    · intro u
      exact div_nonneg (tsum_nonneg (fun k => by
        split_ifs
        · exact density_nonneg r hc i hs k
        · exact le_rfl)) (hmu i).le
    · simp only [equilibrium, tsum_div_const, htm.2, div_self (hmu i).ne']
    · simpa only [equilibrium, ← mul_div_assoc] using hfirst.div_const (mean r c i s)
    · simp_rw [equilibrium, ← mul_div_assoc]
      rw [tsum_div_const, tail_first_moment r hc i hs]
      unfold beta
      ring
  · have h0 : powerSum (2*r-1) s ≠ 0 := (powerSum_pos _ hs).ne'
    have h1 : powerSum (2*r-1) s+c*powerSum (r-1) s ≠ 0 := by
      simpa only [normalizer_eq r c true hs, ↓reduceIte] using
        (normalizer_pos r hc true hs).ne'
    constructor
    · rw [normalizer_eq r c true hs, normalizer_eq r c false hs]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero, quotient]
      field_simp [h0]
      <;> ring
    · intro k hk
      simp only [density, weight, ↓reduceIte, add_zero,
        normalizer_eq r c true hs, normalizer_eq r c false hs,
        quotient, term, hk.ne', Bool.false_eq_true, ↓reduceIte, add_zero]
      field_simp [h0, h1]
      <;> ring

/-- The exact gap law on natural zero counts. -/
def gapLaw (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (hc : 0 < c) (i : Bool)
    (s : ℝ) (hs : 0 < s) : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (density r c i s k), by
    have h := (source_laws_core r hr c hc s hs).1 i
    have hn := ENNReal.ofReal_tsum_of_nonneg h.density_nonnegative
      (by simpa using h.finite_moments 0)
    rw [h.mass_one, ENNReal.ofReal_one] at hn
    exact hn ▸ ENNReal.summable.hasSum⟩

/-- The equilibrium forward wait, including its possible value zero. -/
def waitLaw (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (hc : 0 < c) (i : Bool)
    (s : ℝ) (hs : 0 < s) : PMF ℕ :=
  ⟨fun u => ENNReal.ofReal (equilibrium r c i s u), by
    have h := (source_laws_core r hr c hc s hs).1 i
    have he : Summable (equilibrium r c i s) := h.tail_summable.div_const _
    have hn := ENNReal.ofReal_tsum_of_nonneg h.wait_nonnegative he
    rw [h.wait_mass_one, ENNReal.ofReal_one] at hn
    exact hn ▸ ENNReal.summable.hasSum⟩

private lemma pmf_integrable (p : PMF ℕ) (f : ℕ → ℝ)
    (h : Summable (fun k => (p k).toReal*‖f k‖)) : Integrable f p.toMeasure := by
  rw [← Measure.sum_smul_dirac p.toMeasure]
  simp_rw [p.toMeasure_apply_singleton _ (measurableSet_singleton _)]
  exact integrable_sum_dirac (fun k => p.apply_ne_top k) h

/-- The two actual discrete source laws, their moments and the signed correction. -/
theorem source_laws (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (hc : 0 < c)
    (s : ℝ) (hs : 0 < s) :
    ((∀ i, SourceLaw r c i s) ∧
      normalizer r c true s = (1+c*quotient r s)*normalizer r c false s ∧
      ∀ k : ℕ, 0 < k →
        density r c true s k-density r c false s k =
          c*((k : ℝ)^(r-1)-quotient r s*(k : ℝ)^(2*r-1))*
            Real.exp (-s*k)/normalizer r c true s) ∧
    (∀ i p, Integrable (fun k : ℕ => (k : ℝ)^p) (gapLaw r hr c hc i s hs).toMeasure ∧
      (∫ k : ℕ, (k : ℝ)^p ∂(gapLaw r hr c hc i s hs).toMeasure) = moment r c i s p) ∧
    (∀ i, Integrable (fun u : ℕ => (u : ℝ)) (waitLaw r hr c hc i s hs).toMeasure ∧
      (∫ u : ℕ, (u : ℝ) ∂(waitLaw r hr c hc i s hs).toMeasure) = beta r c i s) := by
  refine ⟨source_laws_core r hr c hc s hs, ?_, ?_⟩
  · intro i p
    have h := (source_laws_core r hr c hc s hs).1 i
    have he (k : ℕ) : (gapLaw r hr c hc i s hs k).toReal = density r c i s k :=
      ENNReal.toReal_ofReal (h.density_nonnegative k)
    have hi : Integrable (fun k : ℕ => (k : ℝ)^p)
        (gapLaw r hr c hc i s hs).toMeasure := by
      apply pmf_integrable
      have hn (k : ℕ) : ‖(k : ℝ)^p‖ = (k : ℝ)^p :=
        Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg k) p)
      simpa only [he, hn, mul_comm] using h.finite_moments p
    refine ⟨hi, ?_⟩
    rw [PMF.integral_eq_tsum _ _ hi]
    simp only [he, smul_eq_mul, moment, mul_comm]
  · intro i
    have h := (source_laws_core r hr c hc s hs).1 i
    have he (u : ℕ) : (waitLaw r hr c hc i s hs u).toReal = equilibrium r c i s u :=
      ENNReal.toReal_ofReal (h.wait_nonnegative u)
    have hi : Integrable (fun u : ℕ => (u : ℝ))
        (waitLaw r hr c hc i s hs).toMeasure := by
      apply pmf_integrable
      have hn (k : ℕ) : ‖(k : ℝ)‖ = (k : ℝ) :=
        Real.norm_of_nonneg (Nat.cast_nonneg k)
      simpa only [he, hn, mul_comm] using h.wait_first_summable
    refine ⟨hi, ?_⟩
    rw [PMF.integral_eq_tsum _ _ hi]
    simpa only [he, smul_eq_mul, mul_comm] using h.wait_mean


private def rawMoment (r : ℕ) (c : ℝ) (i : Bool) (s : ℝ) (p : ℕ) : ℝ :=
  powerSum (2*r-1+p) s + if i then c*powerSum (r-1+p) s else 0

private lemma raw_zero (r : ℕ) (c : ℝ) (i : Bool) {s : ℝ} (hs : 0 < s) :
    rawMoment r c i s 0 = normalizer r c i s := by
  simpa only [rawMoment, Nat.add_zero] using (normalizer_eq r c i hs).symm

private lemma raw_pos (r p : ℕ) {c s : ℝ} (hc : 0 < c) (i : Bool) (hs : 0 < s) :
    0 < rawMoment r c i s p := by
  cases i
  · simpa [rawMoment] using powerSum_pos (2*r-1+p) hs
  · exact add_pos (powerSum_pos _ hs) (mul_pos hc (powerSum_pos _ hs))

private lemma moment_raw (r p : ℕ) (c : ℝ) (i : Bool) {s : ℝ} (hs : 0 < s) :
    moment r c i s p = rawMoment r c i s p / rawMoment r c i s 0 := by
  rw [moment_eq r p c i hs, raw_zero r c i hs]
  rfl

private lemma scaled_raw_limit (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (i : Bool) (p : ℕ) :
    Tendsto (fun s : ℝ => s^(2*r+p)*rawMoment r c i s p) (𝓝[>] 0)
      (𝓝 ((2*r-1+p).factorial : ℝ)) := by
  have hd : 2*r-1+p+1 = 2*r+p := by omega
  have hm := scaled_powerSum_limit (2*r-1+p)
  rw [hd] at hm
  cases i
  · simpa [rawMoment] using hm
  · have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hz : Tendsto (fun s : ℝ =>
        s^r*(s^(r-1+p+1)*powerSum (r-1+p) s)) (𝓝[>] 0) (𝓝 0) := by
      simpa [zero_pow (by omega : r ≠ 0)] using
        (hid.pow r).mul (scaled_powerSum_limit (r-1+p))
    have h := hm.add (hz.const_mul c)
    simp only [mul_zero, add_zero] at h
    convert h using 1
    funext s
    dsimp [rawMoment]
    have he : 2*r+p = r+(r-1+p+1) := by omega
    simp only [he, pow_add]
    ring

private lemma scaled_mean_eq (r : ℕ) {c s : ℝ} (hc : 0 < c) (i : Bool)
    (hs : 0 < s) :
    s*mean r c i s =
      (s^(2*r+1)*rawMoment r c i s 1)/(s^(2*r)*rawMoment r c i s 0)+s := by
  rw [mean, moment_raw r 1 c i hs]
  have hn := (raw_pos r 0 hc i hs).ne'
  simp only [pow_succ]
  field_simp [hs.ne', hn]
  <;> ring

private lemma scaled_beta_eq (r : ℕ) {c s : ℝ} (hc : 0 < c) (i : Bool)
    (hs : 0 < s) :
    s*beta r c i s =
      (s^(2*r+2)*rawMoment r c i s 2+s*(s^(2*r+1)*rawMoment r c i s 1)) /
        (2*(s^(2*r+1)*rawMoment r c i s 1+s*(s^(2*r)*rawMoment r c i s 0))) := by
  rw [beta, mean, moment_raw r 2 c i hs, moment_raw r 1 c i hs]
  have h0 := raw_pos r 0 hc i hs
  have h1 := raw_pos r 1 hc i hs
  have h2 := raw_pos r 2 hc i hs
  have hsum : rawMoment r c i s 1+rawMoment r c i s 0 ≠ 0 :=
    (add_pos h1 h0).ne'
  simp only [pow_add, pow_one, pow_two]
  field_simp [hs.ne', h0.ne']
  <;> ring

private lemma scalar_limits (r : ℕ) (hr : 1 ≤ r) {c : ℝ} (hc : 0 < c) :
    (∀ i, Tendsto (fun s : ℝ => s^(2*r)*normalizer r c i s)
      (𝓝[>] 0) (𝓝 ((2*r-1).factorial : ℝ))) ∧
    Tendsto (fun s : ℝ => quotient r s/s^r)
      (𝓝[>] 0) (𝓝 ((r-1).factorial/(2*r-1).factorial : ℝ)) ∧
    (∀ i, Tendsto (fun s : ℝ => s*mean r c i s)
      (𝓝[>] 0) (𝓝 ((2*r).factorial/(2*r-1).factorial : ℝ))) ∧
    (∀ i, Tendsto (fun s : ℝ => s*(1+beta r c i s))
      (𝓝[>] 0) (𝓝 ((2*r+1).factorial/(2*(2*r).factorial) : ℝ))) := by
  have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h0 (i : Bool) := scaled_raw_limit r hr c i 0
  simp only [Nat.add_zero] at h0
  have h1 (i : Bool) := scaled_raw_limit r hr c i 1
  have h2 (i : Bool) := scaled_raw_limit r hr c i 2
  have he1 : 2*r-1+1 = 2*r := by omega
  have he2 : 2*r-1+2 = 2*r+1 := by omega
  rw [he1] at h1
  rw [he2] at h2
  have ha0 : ((2*r-1).factorial : ℝ) ≠ 0 := by positivity
  have ha1 : (2*((2*r).factorial : ℝ)) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    apply (h0 i).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [raw_zero r c i hs]
  · have he : r-1+1 = r := by omega
    have hl := scaled_powerSum_limit (r-1)
    rw [he] at hl
    have h := hl.div (h0 false) ha0
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    change 0 < s at hs
    simp only [rawMoment, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, add_zero,
      quotient]
    have hp : 2*r = r+r := by omega
    change (s^r*powerSum (r-1) s)/(s^(2*r)*powerSum (2*r-1) s) =
      powerSum (r-1) s/powerSum (2*r-1) s/s^r
    rw [show s^(2*r) = s^r*s^r by rw [hp, pow_add]]
    field_simp [hs.ne', (powerSum_pos (2*r-1) hs).ne']
  · intro i
    have h := ((h1 i).div (h0 i) ha0).add hid
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (scaled_mean_eq r hc i hs).symm
  · intro i
    have hb := ((h2 i).add (hid.mul (h1 i))).div
      (((h1 i).add (hid.mul (h0 i))).const_mul 2) (by
        simpa using ha1)
    simp only [zero_mul, add_zero] at hb
    have h := hid.add hb
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    change s+(s^(2*r+2)*rawMoment r c i s 2+
      s*(s^(2*r+1)*rawMoment r c i s 1)) /
      (2*(s^(2*r+1)*rawMoment r c i s 1+
        s*(s^(2*r)*rawMoment r c i s 0))) = s*(1+beta r c i s)
    rw [← scaled_beta_eq r hc i hs]
    ring

/-- One source-only neighborhood works for both labels and all subsequent phase caps. -/
theorem common_scalar_neighborhood (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (hc : 0 < c) :
    ∃ sStar zMinus zPlus G Cmu Cbeta : ℝ,
      0 < sStar ∧ sStar < 1 ∧ 0 < zMinus ∧ 0 < zPlus ∧ 0 < G ∧
      0 < Cmu ∧ 0 < Cbeta ∧
      ∀ s : ℝ, 0 < s → s < sStar →
        (∀ i, zMinus/s^(2*r) ≤ normalizer r c i s ∧
          normalizer r c i s ≤ zPlus/s^(2*r) ∧
          mean r c i s ≤ Cmu/s ∧ 1+beta r c i s ≤ Cbeta/s) ∧
        quotient r s ≤ G*s^r := by
  let a0 : ℝ := (2*r-1).factorial
  let a1 : ℝ := (2*r).factorial
  let a2 : ℝ := (2*r+1).factorial
  let b : ℝ := (r-1).factorial
  have ha0 : 0 < a0 := by dsimp [a0]; positivity
  have ha1 : 0 < a1 := by dsimp [a1]; positivity
  have ha2 : 0 < a2 := by dsimp [a2]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  let G : ℝ := b/a0+1
  let Cmu : ℝ := a1/a0+1
  let Cbeta : ℝ := a2/(2*a1)+1
  have hlim := scalar_limits r hr hc
  have he (i : Bool) : ∀ᶠ s : ℝ in 𝓝[>] 0,
      a0/2 < s^(2*r)*normalizer r c i s ∧
      s^(2*r)*normalizer r c i s < 2*a0 ∧
      s*mean r c i s < Cmu ∧ s*(1+beta r c i s) < Cbeta := by
    have hl := (tendsto_order.1 (hlim.1 i)).1 (a0/2) (by change a0/2 < a0; linarith)
    have hu := (tendsto_order.1 (hlim.1 i)).2 (2*a0) (by change a0 < 2*a0; linarith)
    have hm := (tendsto_order.1 (hlim.2.2.1 i)).2 Cmu (by dsimp [Cmu]; linarith)
    have hw := (tendsto_order.1 (hlim.2.2.2 i)).2 Cbeta (by dsimp [Cbeta]; linarith)
    filter_upwards [hl, hu, hm, hw] with s hsl hsu hsm hsw
    exact ⟨hsl, hsu, hsm, hsw⟩
  have hq := (tendsto_order.1 hlim.2.1).2 G (by dsimp [G]; linarith)
  have hall : ∀ᶠ s : ℝ in 𝓝[>] 0,
      (∀ i, a0/2 < s^(2*r)*normalizer r c i s ∧
        s^(2*r)*normalizer r c i s < 2*a0 ∧
        s*mean r c i s < Cmu ∧ s*(1+beta r c i s) < Cbeta) ∧
      quotient r s/s^r < G := by
    filter_upwards [he false, he true, hq] with s hfalse htrue hqs
    refine ⟨?_, hqs⟩
    intro i
    cases i
    · exact hfalse
    · exact htrue
  obtain ⟨t, ht, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  let sStar : ℝ := min (t/2) (1/2)
  have hstar : 0 < sStar := lt_min (half_pos ht) (by norm_num)
  have hst : sStar < t := (min_le_left _ _).trans_lt (half_lt_self ht)
  have hs1 : sStar < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨sStar, a0/2, 2*a0, G, Cmu, Cbeta, hstar, hs1,
    by positivity, by positivity, by dsimp [G]; positivity,
    by dsimp [Cmu]; positivity, by dsimp [Cbeta]; positivity, ?_⟩
  intro s hs hss
  have h := hsub ⟨hs, hss.trans hst⟩
  constructor
  · intro i
    have hi := h.1 i
    have hp : 0 < s^(2*r) := pow_pos hs _
    refine ⟨(div_le_iff₀ hp).2 ?_, (le_div_iff₀ hp).2 ?_,
      (le_div_iff₀ hs).2 ?_, (le_div_iff₀ hs).2 ?_⟩
    · simpa only [mul_comm] using hi.1.le
    · simpa only [mul_comm] using hi.2.1.le
    · simpa only [mul_comm] using hi.2.2.1.le
    · simpa only [mul_comm] using hi.2.2.2.le
  · exact ((div_lt_iff₀ (pow_pos hs r)).1 h.2).le

#print axioms source_laws
#print axioms common_scalar_neighborhood

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CriticalRenewalSource

end
end

section
/-! The full finite renewal table, its fresh row realization, and complete-gap law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalTable

namespace Phase
abbrev T (J : ℕ) := Fin (J + 1)
def first (J : ℕ) : T J := ⟨0, by omega⟩
def dead (J : ℕ) : T J := ⟨J, by omega⟩
def advance {J : ℕ} (z : T J) : T J := ⟨min (z.val + 1) J, by omega⟩
def step {J : ℕ} (z : T J) (b : Bool) : T J := if b then advance z else z
def coin {J : ℕ} (z : T J) : PMF Bool :=
  PMF.bernoulli (GeometricPhaseOccupation.success z.val)
    (by unfold GeometricPhaseOccupation.success; exact pow_le_one₀ (by norm_num) (by norm_num))
end Phase

abbrev Evidence (H : ℕ) := ↥(Finset.Ioo (-(H : ℤ)) (H : ℤ))
/-- Exactly one wait, two terminal labels, and the full evidence/phase product. -/
abbrev State (H J : ℕ) := Option (Bool ⊕ (Evidence H × Phase.T J))
def wait {H J : ℕ} : State H J := none
def label {H J : ℕ} (b : Bool) : State H J := some (.inl b)
def active {H J : ℕ} (e : Evidence H) (z : Phase.T J) : State H J := some (.inr (e,z))

def initialEvidence {H : ℕ} (hH : 0 < H) : Evidence H :=
  ⟨0, by simp only [Finset.mem_Ioo]; constructor <;> omega⟩

/-- No overshoot value is retained after either threshold is reached. -/
def target (H J : ℕ) (u : ℤ) : State H J :=
  if hupper : (H : ℤ) ≤ u then label true
  else if hlower : u ≤ -(H : ℤ) then label false
  else active ⟨u, by simp only [Finset.mem_Ioo]; omega⟩ (Phase.first J)

/-- These are immutable row entries; this structure is not part of the carrier. -/
structure Tick (J : ℕ) where
  lower : Phase.T J → ℤ
  prob : Phase.T J → ℝ≥0
  prob_le_one : ∀ z, prob z ≤ 1

def Tick.coin {J : ℕ} (t : Tick J) (z : Phase.T J) : PMF Bool :=
  PMF.bernoulli (t.prob z) (t.prob_le_one z)

def Tick.increment {J : ℕ} (t : Tick J) (z : Phase.T J) (b : Bool) : ℤ :=
  t.lower z + if b then 1 else 0

/-- The whole stochastic table. Labels are totalized by self loops. -/
def row {H J : ℕ} (hH : 0 < H) (t : Tick J) : State H J → Bool → PMF (State H J)
  | none, false => PMF.pure wait
  | none, true => PMF.pure (active (initialEvidence hH) (Phase.first J))
  | some (.inl b), _ => PMF.pure (label b)
  | some (.inr (e,z)), false =>
      (GeometricPhaseOccupation.finiteCappedRow J z).map (active e)
  | some (.inr (e,z)), true =>
      (t.coin z).map fun b => target H J (e.val + t.increment z b)


/-- Deterministic realization of a row by one fresh coin; the coin is not retained. -/
def next {H J : ℕ} (hH : 0 < H) (t : Tick J) : State H J → Bool → Bool → State H J
  | none, false, _ => wait
  | none, true, _ => active (initialEvidence hH) (Phase.first J)
  | some (.inl b), _, _ => label b
  | some (.inr (e,z)), false, b => active e (Phase.step z b)
  | some (.inr (e,z)), true, b => target H J (e.val + t.increment z b)

/-- On dead zeros both possible fresh outcomes merge into the same dead state. -/
def coin {H J : ℕ} (t : Tick J) : State H J → Bool → PMF Bool
  | some (.inr (_,z)), false => Phase.coin z
  | some (.inr (_,z)), true => t.coin z
  | _, _ => PMF.pure false

theorem phase_coin_row (J : ℕ) (z : Phase.T J) :
    ((Phase.coin z).map (Phase.step z)) = GeometricPhaseOccupation.finiteCappedRow J z := by
  unfold Phase.coin
  by_cases hz : z.val < J
  · simp only [GeometricPhaseOccupation.finiteCappedRow,
      GeometricPhaseOccupation.cappedRow, hz, ↓reduceIte,
      GeometricPhaseOccupation.zeroRow, PMF.map_comp]
    congr 1
    funext b
    apply Fin.ext
    cases b <;> simp [Function.comp_def, Phase.step, Phase.advance,
      GeometricPhaseOccupation.capState, Nat.min_eq_left (by omega : z.val ≤ J)]
  · have he : z = Phase.dead J := Fin.ext (by dsimp [Phase.dead]; omega)
    subst z
    have hm : Phase.step (Phase.dead J) = Function.const Bool (Phase.dead J) := by
      funext b
      cases b <;> simp [Phase.step, Phase.advance, Phase.dead]
    rw [hm, PMF.map_const]
    simp [GeometricPhaseOccupation.finiteCappedRow,
      GeometricPhaseOccupation.cappedRow, Phase.dead,
      GeometricPhaseOccupation.capState, PMF.map_const, PMF.pure_map]

/-- Every deterministic coin realization has exactly the declared stochastic row. -/
theorem fresh_row {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (s : State H J) (x : Bool) :
    (coin t s x).map (next hH t s x) = row hH t s x := by
  cases s with
  | none => cases x <;> simp [coin, next, row, wait, PMF.pure_map]
  | some s =>
    cases s with
    | inl b => cases x <;> simp [coin, next, row, label, PMF.pure_map]
    | inr ez =>
      rcases ez with ⟨e,z⟩
      cases x with
      | false =>
        change ((Phase.coin z).map fun b => active e (Phase.step z b)) = _
        change ((Phase.coin z).map ((active e) ∘ Phase.step z)) = _
        rw [← PMF.map_comp, phase_coin_row]
        rfl
      | true => rfl

/-- A finite word always charges one transition per actual bit. -/
def wordLaw {H J : ℕ} (hH : 0 < H) (t : Tick J) :
    State H J → List Bool → PMF (State H J)
  | s, [] => PMF.pure s
  | s, b :: w => ((coin t s b).map (next hH t s b)).bind fun s' => wordLaw hH t s' w

private lemma wordLaw_append {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (s : State H J) (v w : List Bool) :
    wordLaw hH t s (v ++ w) = (wordLaw hH t s v).bind fun s' => wordLaw hH t s' w := by
  induction v generalizing s with
  | nil => simp [wordLaw]
  | cons b v ih => simp only [List.cons_append, wordLaw, ih, PMF.bind_bind]

private lemma zeroLaw {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (e : Evidence H) (k : ℕ) :
    wordLaw hH t (active e (Phase.first J)) (List.replicate k false) =
      (GeometricPhaseOccupation.finiteCappedLaw J k).map (active e) := by
  induction k with
  | zero => simp [wordLaw, GeometricPhaseOccupation.finiteCappedLaw, Phase.first, PMF.pure_map]
  | succ k ih =>
    rw [List.replicate_succ', wordLaw_append, ih]
    simp only [PMF.bind_map, Function.comp_def, wordLaw, fresh_row, PMF.bind_pure,
      row, active, GeometricPhaseOccupation.finiteCappedLaw, PMF.map_bind]

/-- The same zero-chain supplies the phase used by the tick, also for k=0. -/
theorem complete_gap_row {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (e : Evidence H) (k : ℕ) :
    wordLaw hH t (active e (Phase.first J)) (List.replicate k false ++ [true]) =
      (GeometricPhaseOccupation.finiteCappedLaw J k).bind fun z =>
        (t.coin z).map fun b => target H J (e.val + t.increment z b) := by
  rw [wordLaw_append, zeroLaw]
  simp only [PMF.bind_map, Function.comp_def, wordLaw, fresh_row, PMF.bind_pure, row, active]

/-- A duration and its own terminal increment are sampled jointly. -/
def pairLaw {J : ℕ} (f : PMF ℕ) (t : Tick J) : PMF (ℕ × ℤ) :=
  f.bind fun k => (GeometricPhaseOccupation.finiteCappedLaw J k).bind fun z =>
    (t.coin z).map fun b => (k, t.increment z b)

/-- The joint potential law drives the literal complete-gap table, with no
    independence assumption between its duration and its increment. -/
theorem random_gap_row {H J : ℕ} (hH : 0 < H) (f : PMF ℕ)
    (t : Tick J) (e : Evidence H) :
    (f.bind fun k => wordLaw hH t (active e (Phase.first J))
      (List.replicate k false ++ [true])) =
        (pairLaw f t).map (fun ku => target H J (e.val + ku.2)) := by
  simp only [complete_gap_row, pairLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- All listed configurations count, whether or not a row can reach them. -/
theorem full_state_count (H J : ℕ) (hH : 0 < H) :
    Fintype.card (State H J) = 3 + (2 * H - 1) * (J + 1) := by
  have he : Fintype.card (Evidence H) = 2 * H - 1 := by
    rw [Fintype.card_coe, Int.card_Ioo]
    omega
  simp [State, Fintype.card_option, Fintype.card_sum, Fintype.card_prod, he, Phase.T]
  omega

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalTable

end
end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalPaths
open CriticalRenewalTable

/-- A finite block of fresh zero outcomes and its one closing-tick outcome.
    These are proof coordinates, not retained observer data. -/
structure Block where
  zeros : List Bool
  tick : Bool
  deriving Countable

def phaseAt (J : ℕ) (b : Block) : ℕ → Phase.T J
  | 0 => Phase.first J
  | k + 1 => Phase.step (phaseAt J b k) (b.zeros[k]?.getD false)

def increment {J : ℕ} (t : Tick J) (b : Block) : ℤ :=
  t.increment (phaseAt J b b.zeros.length) b.tick

attribute [local simp] phaseAt phaseAt.eq_def

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalPaths

end
end
