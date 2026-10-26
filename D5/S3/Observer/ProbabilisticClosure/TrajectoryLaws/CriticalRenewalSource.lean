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
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

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

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CriticalRenewalSource
