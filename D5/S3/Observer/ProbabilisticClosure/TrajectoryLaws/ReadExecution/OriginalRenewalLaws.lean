/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal degree-nine renewal PMFs with the stationary wait at zero. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalTable

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped ENNReal BigOperators
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalRenewalLaws
open CriticalRenewalSource

/-- The two literal public shapes at the same parameter. -/
def shape (i : Bool) (x : ℝ) : ℝ :=
  x^9 + if i then
    (55800726477138*x - 224986136658885*x^2 + 420664314485485*x^3 -
      540138133491075*x^4 + 518234977000797*x^5 - 254383031435085*x^6 +
      77668004560980*x^7 + 43377331415040*x^8) / (35*10^24) else 0

def weight (q : ℝ) (i : Bool) (k : ℕ) : ℝ :=
  if k = 0 then 0 else shape i k * q^k

def normalizer (q : ℝ) (i : Bool) : ℝ := ∑' k, weight q i k

def density (q : ℝ) (i : Bool) (k : ℕ) : ℝ := weight q i k / normalizer q i

/-- K counts zeros; the intertick length is K+1. -/
def mean (q : ℝ) (i : Bool) : ℝ := ∑' k : ℕ, (k+1 : ℝ) * density q i k

def tail (q : ℝ) (i : Bool) (u : ℕ) : ℝ :=
  ∑' k : ℕ, if u ≤ k then density q i k else 0

def equilibrium (q : ℝ) (i : Bool) (u : ℕ) : ℝ := tail q i u / mean q i

private theorem shape_positive (i : Bool) {x : ℝ} (hx : 1 ≤ x) : 0 < shape i x := by
  have hx0 : 0 ≤ x := by linarith
  have h9 : 0 < x^9 := pow_pos (by linarith) _
  have h2 : x^2 ≤ x^9 := pow_le_pow_right₀ hx (by decide)
  have h4 : x^4 ≤ x^9 := pow_le_pow_right₀ hx (by decide)
  have h6 : x^6 ≤ x^9 := pow_le_pow_right₀ hx (by decide)
  cases i
  · simpa [shape] using h9
  · have hp : 0 ≤ 55800726477138*x + 420664314485485*x^3 +
        518234977000797*x^5 + 77668004560980*x^7 + 43377331415040*x^8 := by positivity
    simp only [shape, Bool.true_eq, ↓reduceIte]
    norm_num only [Nat.reducePow, Nat.reduceMul]
    linarith

private theorem weight_nonnegative {q : ℝ} (hq : 0 < q) (i : Bool) (k : ℕ) :
    0 ≤ weight q i k := by
  by_cases hk : k = 0
  · simp [weight, hk]
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
    simpa only [weight, hk, ↓reduceIte] using
      (mul_pos (shape_positive i hk1) (pow_pos hq k)).le

private theorem weighted_summable {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (i : Bool) (p : ℕ) : Summable fun k : ℕ => (k : ℝ)^p * weight q i k := by
  have hs : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  have ht (m : ℕ) : Summable (fun k : ℕ =>
      if k = 0 then (0 : ℝ) else (k : ℝ)^m * q^k) := by
    convert summable_term m hs using 1
    funext k
    simp only [term, neg_neg, mul_comm (Real.log q), Real.exp_nat_mul, Real.exp_log hq]
  have he (m k : ℕ) : (k : ℝ)^p *
      (if k = 0 then (0 : ℝ) else (k : ℝ)^m * q^k) =
      if k = 0 then 0 else (k : ℝ)^(p+m) * q^k := by
    split_ifs <;> simp [pow_add, mul_assoc]
  cases i
  · simpa only [weight, shape, Bool.false_eq_true, ↓reduceIte, add_zero,
      mul_ite, mul_zero, ← he] using ht (p+9)
  · have h1 := ((ht (p+1)).mul_left 55800726477138).sub
        ((ht (p+2)).mul_left 224986136658885)
    have h2 := h1.add ((ht (p+3)).mul_left 420664314485485)
    have h3 := h2.sub ((ht (p+4)).mul_left 540138133491075)
    have h4 := h3.add ((ht (p+5)).mul_left 518234977000797)
    have h5 := h4.sub ((ht (p+6)).mul_left 254383031435085)
    have h6 := h5.add ((ht (p+7)).mul_left 77668004560980)
    have h7 := h6.add ((ht (p+8)).mul_left 43377331415040)
    have hh := (ht (p+9)).add (h7.div_const (35*10^24))
    convert hh using 1
    funext k
    by_cases hk : k = 0
    · simp [weight, hk]
    · simp only [weight, shape, hk, ↓reduceIte, pow_add]
      ring

private theorem normalizer_positive {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (i : Bool) :
    0 < normalizer q i := by
  apply (show Summable (weight q i) by simpa using weighted_summable hq hq1 i 0).tsum_pos
    (weight_nonnegative hq i) 1
  simp only [weight, one_ne_zero, ↓reduceIte, Nat.cast_one, pow_one]
  exact mul_pos (shape_positive i le_rfl) hq

private theorem density_summable {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (i : Bool) (p : ℕ) : Summable fun k : ℕ => (k : ℝ)^p * density q i k := by
  simpa only [density, mul_div_assoc] using (weighted_summable hq hq1 i p).div_const _

private theorem density_nonnegative {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (i : Bool) (k : ℕ) : 0 ≤ density q i k :=
  div_nonneg (weight_nonnegative hq i k) (normalizer_positive hq hq1 i).le

private theorem density_mass {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (i : Bool) :
    ∑' k, density q i k = 1 := by
  simp only [density, tsum_div_const]
  exact div_self (normalizer_positive hq hq1 i).ne'

private theorem mean_positive {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (i : Bool) :
    0 < mean q i := by
  have he : mean q i = (∑' k : ℕ, (k : ℝ) * density q i k) + 1 := by
    simp only [mean, add_mul, one_mul]
    rw [Summable.tsum_add (by simpa using density_summable hq hq1 i 1)
      (by simpa using density_summable hq hq1 i 0), density_mass hq hq1 i]
  rw [he]
  exact add_pos_of_nonneg_of_pos (tsum_nonneg fun k =>
    mul_nonneg (Nat.cast_nonneg _) (density_nonnegative hq hq1 i k)) zero_lt_one

private theorem tail_mass {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (i : Bool) :
    Summable (tail q i) ∧ ∑' u, tail q i u = mean q i := by
  have hs : Summable fun k : ℕ => ((k : ℝ)+1) * density q i k := by
    simpa only [add_mul, one_mul, pow_one, pow_zero] using
      (density_summable hq hq1 i 1).add (density_summable hq hq1 i 0)
  have h := weighted_tails (density q i) (density_nonnegative hq hq1 i) 0
    (by simpa using hs)
  change Summable (fun u => ∑' k, if u ≤ k then density q i k else 0) ∧ _
  simpa only [pow_zero, one_mul, mul_one, sum_const, card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mean, tail] using h

/-- Exact positive-gap law for the literal degree-nine shape. -/
def gapLaw (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (i : Bool) : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (density q i k), by
    have h := ENNReal.ofReal_tsum_of_nonneg (density_nonnegative hq hq1 i)
      (by simpa using density_summable hq hq1 i 0)
    rw [density_mass hq hq1 i, ENNReal.ofReal_one] at h
    exact h ▸ ENNReal.summable.hasSum⟩

/-- The original stationary first wait includes the value zero. -/
def waitLaw (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (i : Bool) : PMF ℕ :=
  ⟨fun u => ENNReal.ofReal (equilibrium q i u), by
    have hn (u : ℕ) : 0 ≤ equilibrium q i u :=
      div_nonneg (tsum_nonneg fun k => by
        split_ifs <;> first | exact density_nonnegative hq hq1 i k | exact le_rfl)
        (mean_positive hq hq1 i).le
    have hs := (tail_mass hq hq1 i).1.div_const (mean q i)
    have hm : ∑' u, equilibrium q i u = 1 := by
      change (∑' u, tail q i u / mean q i) = 1
      rw [tsum_div_const, (tail_mass hq hq1 i).2,
        div_self (mean_positive hq hq1 i).ne']
    have h := ENNReal.ofReal_tsum_of_nonneg hn hs
    rw [hm, ENNReal.ofReal_one] at h
    exact h ▸ ENNReal.summable.hasSum⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.OriginalRenewalLaws
