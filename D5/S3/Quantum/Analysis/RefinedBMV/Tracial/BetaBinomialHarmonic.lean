/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/BetaBinomialHarmonic
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Harmonic expectations for finite beta-binomial likelihood estimates. -/

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.Binomial

open Finset

namespace RefinedBMV.Tracial

noncomputable section

private theorem multichoose_add (a b : ℝ) (n : ℕ) :
    Ring.multichoose (a + b) n =
      ∑ ij ∈ HasAntidiagonal.antidiagonal n,
        Ring.multichoose a ij.1 * Ring.multichoose b ij.2 := by
  have h := Ring.add_choose_eq (r := -a) (s := -b) n (Commute.all _ _)
  rw [← neg_add] at h
  simp only [Ring.choose_neg'] at h
  apply (smul_left_cancel ((n : ℤ).negOnePow))
  calc
    _ = ∑ ij ∈ HasAntidiagonal.antidiagonal n,
        (ij.1 : ℤ).negOnePow • Ring.multichoose a ij.1 *
          ((ij.2 : ℤ).negOnePow • Ring.multichoose b ij.2) := h
    _ = _ := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun ij hij ↦ ?_
      rw [smul_mul_smul_comm, ← Int.negOnePow_add, ← Nat.cast_add,
        Finset.HasAntidiagonal.mem_antidiagonal.mp hij]

private theorem multichoose_eq_prod (a : ℝ) (n : ℕ) :
    Ring.multichoose a n = (∏ k ∈ range n, (a + k)) / n.factorial := by
  have hprod : (ascPochhammer ℝ n).eval a = ∏ k ∈ range n, (a + k) := by
    induction n with
    | zero => simp
    | succ n ih => rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))).mpr
  rw [mul_comm, h, hprod]

private theorem hasDerivAt_multichoose {a : ℝ} (ha : 0 < a) (n : ℕ) :
    HasDerivAt (fun t : ℝ ↦ Ring.multichoose t n)
      (Ring.multichoose a n * ∑ k ∈ range n, (a + k)⁻¹) a := by
  simp only [multichoose_eq_prod]
  have hterm (k : ℕ) (_ : k ∈ range n) :
      HasDerivAt (fun t : ℝ ↦ t + k) 1 a := (hasDerivAt_id a).add_const (k : ℝ)
  convert (HasDerivAt.fun_finsetProd hterm).div_const (n.factorial : ℝ) using 1
  rw [div_mul_eq_mul_div, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [smul_eq_mul, mul_one, ← Finset.prod_erase_mul _ _ hk, mul_assoc,
    mul_inv_cancel₀ (by positivity), mul_one]

/-- Differentiating the rising-factorial convolution gives the exact expectation
of a finite reciprocal sum under the beta-binomial law. -/
theorem betaBinomial_harmonic_expectation {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∑ ij ∈ HasAntidiagonal.antidiagonal n,
      Ring.multichoose a ij.1 * Ring.multichoose b ij.2 *
        (∑ k ∈ range ij.1, (a + k)⁻¹) =
      Ring.multichoose (a + b) n * ∑ k ∈ range n, (a + b + k)⁻¹ := by
  have hsum := HasDerivAt.fun_sum (u := HasAntidiagonal.antidiagonal n)
    (fun ij _ ↦ (hasDerivAt_multichoose ha ij.1).mul_const (Ring.multichoose b ij.2))
  have hbase := (hasDerivAt_multichoose (add_pos ha hb) n).comp a ((hasDerivAt_id a).add_const b)
  have heq : (fun x : ℝ ↦ ∑ ij ∈ HasAntidiagonal.antidiagonal n,
      Ring.multichoose x ij.1 * Ring.multichoose b ij.2) =
        fun x : ℝ ↦ Ring.multichoose (x + b) n := by
    funext x
    exact (multichoose_add x b n).symm
  rw [heq] at hsum
  simpa only [mul_assoc, mul_left_comm, mul_comm, mul_one, one_mul] using hsum.unique hbase


private def reciprocalSum (n : ℕ) : ℝ := ∑ k ∈ range n, ((k : ℝ) + 1)⁻¹

private theorem log_sub_reciprocalSum_le {j m : ℕ} (hj : 0 < j) (hjm : j ≤ m) :
    Real.log j - reciprocalSum j ≤ Real.log m - reciprocalSum m := by
  induction hjm with
  | refl => rfl
  | @step m hjm ih =>
    refine ih.trans ?_
    have hm : 0 < (m : ℝ) := by exact_mod_cast hj.trans_le hjm
    have hstep := Real.log_le_sub_one_of_pos (div_pos hm (by positivity : 0 < (m : ℝ) + 1))
    rw [Real.log_div hm.ne' (by positivity),
      show (m : ℝ) / ((m : ℝ) + 1) - 1 = -((m : ℝ) + 1)⁻¹ by
        field_simp
        ring] at hstep
    simp only [reciprocalSum, Finset.sum_range_succ, Nat.cast_succ] at *
    linarith only [hstep]

private theorem reciprocalSum_add (a n : ℕ) (ha : 0 < a) :
    reciprocalSum (a + n - 1) =
      reciprocalSum (a - 1) + ∑ k ∈ range n, ((a : ℝ) + k)⁻¹ := by
  have hae : ((a - 1 : ℕ) : ℝ) + 1 = a := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  unfold reciprocalSum
  rw [show a + n - 1 = (a - 1) + n by omega, Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Nat.cast_add]
  congr 1
  linarith only [hae]

/-- The mean log likelihood for increasing the first beta-binomial parameter
is bounded by explicit reciprocal sums. This removes integration from the bound. -/
theorem betaBinomial_weighted_log_le (a b n : ℕ) (ha : 1 < a) (hb : 0 < b) :
    ∑ ij ∈ HasAntidiagonal.antidiagonal n,
      Ring.multichoose (a : ℝ) ij.1 * Ring.multichoose (b : ℝ) ij.2 *
        Real.log (((a + ij.1 - 1 : ℕ) : ℝ) / ((a + b + n - 1 : ℕ) : ℝ)) ≤
      -(Ring.multichoose ((a : ℝ) + b) n * ∑ k ∈ range b, ((a : ℝ) + k)⁻¹) := by
  let weight (ij : ℕ × ℕ) : ℝ :=
    Ring.multichoose (a : ℝ) ij.1 * Ring.multichoose (b : ℝ) ij.2
  let base : ℝ := ∑ k ∈ range b, ((a : ℝ) + k)⁻¹
  let norm : ℝ := ∑ k ∈ range n, ((a : ℝ) + b + k)⁻¹
  let sample (i : ℕ) : ℝ := ∑ k ∈ range i, ((a : ℝ) + k)⁻¹
  have hweight (ij : ℕ × ℕ) : 0 ≤ weight ij := by
    dsimp [weight]
    simp only [multichoose_eq_prod]
    positivity
  have hpoint (ij : ℕ × ℕ) (hij : ij ∈ HasAntidiagonal.antidiagonal n) :
      Real.log (((a + ij.1 - 1 : ℕ) : ℝ) / ((a + b + n - 1 : ℕ) : ℝ)) ≤
        sample ij.1 - (base + norm) := by
    have hi := (Finset.HasAntidiagonal.mem_antidiagonal.mp hij)
    rw [Real.log_div (by exact_mod_cast (by omega : a + ij.1 - 1 ≠ 0))
      (by exact_mod_cast (by omega : a + b + n - 1 ≠ 0))]
    have h := log_sub_reciprocalSum_le (show 0 < a + ij.1 - 1 by omega)
      (show a + ij.1 - 1 ≤ a + b + n - 1 by omega)
    rw [reciprocalSum_add a ij.1 (by omega),
      reciprocalSum_add (a + b) n (by omega), reciprocalSum_add a b (by omega)] at h
    push_cast at h
    dsimp [sample, base, norm]
    linarith only [h]
  have htotal : ∑ ij ∈ HasAntidiagonal.antidiagonal n, weight ij =
      Ring.multichoose ((a : ℝ) + b) n := (multichoose_add a b n).symm
  have hmean := betaBinomial_harmonic_expectation (a := (a : ℝ)) (b := (b : ℝ))
    (by exact_mod_cast (by omega : 0 < a)) (by exact_mod_cast hb) n
  change ∑ ij ∈ HasAntidiagonal.antidiagonal n, weight ij * sample ij.1 =
    Ring.multichoose ((a : ℝ) + b) n * norm at hmean
  calc
    _ ≤ ∑ ij ∈ HasAntidiagonal.antidiagonal n, weight ij * (sample ij.1 - (base + norm)) :=
      Finset.sum_le_sum fun ij hij ↦ mul_le_mul_of_nonneg_left (hpoint ij hij) (hweight ij)
    _ = _ := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, htotal, hmean]
      dsimp [base]
      ring


/-- The beta-binomial mass at the two counts of a fixed-size split. -/
def betaBinomialMass (a b : ℝ) (n : ℕ) (ij : ℕ × ℕ) : ℝ :=
  (Ring.multichoose a ij.1 * Ring.multichoose b ij.2) / Ring.multichoose (a + b) n

private theorem multichoose_pos {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < Ring.multichoose a n := by
  rw [multichoose_eq_prod]
  exact div_pos (Finset.prod_pos fun _ _ ↦ by positivity) (by positivity)

theorem betaBinomialMass_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (ij : ℕ × ℕ) : 0 < betaBinomialMass a b n ij :=
  div_pos (mul_pos (multichoose_pos ha _) (multichoose_pos hb _))
    (multichoose_pos (add_pos ha hb) n)

theorem sum_betaBinomialMass {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∑ ij ∈ HasAntidiagonal.antidiagonal n, betaBinomialMass a b n ij = 1 := by
  simp only [betaBinomialMass, div_eq_mul_inv, ← Finset.sum_mul, ← multichoose_add,
    mul_inv_cancel₀ (multichoose_pos (add_pos ha hb) n).ne']

private theorem multichoose_add_one_mul (a : ℝ) (n : ℕ) :
    Ring.multichoose (a + 1) n * a = Ring.multichoose a n * (a + n) := by
  simp only [multichoose_eq_prod]
  have h : (∏ k ∈ range n, ((a + 1) + k)) * a =
      (∏ k ∈ range n, (a + k)) * (a + n) := by
    rw [← Finset.prod_range_succ]
    conv_rhs => rw [Finset.prod_range_succ']
    simp only [Nat.cast_zero, add_zero, Nat.cast_succ]
    congr 1
    exact Finset.prod_congr rfl fun _ _ ↦ by ring
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hfac]
  simpa only [mul_comm a] using h

private theorem betaBinomialMass_ratio_shift {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (ij : ℕ × ℕ) :
    betaBinomialMass (a + 1) b n ij / betaBinomialMass a b n ij =
      ((a + b) / a) * ((a + ij.1) / (a + b + n)) := by
  have hs := multichoose_add_one_mul a ij.1
  have hn := multichoose_add_one_mul (a + b) n
  have he : a + 1 + b = a + b + 1 := by ring
  unfold betaBinomialMass
  rw [show Ring.multichoose (a + 1) ij.1 =
      Ring.multichoose a ij.1 * (a + ij.1) / a from (eq_div_iff ha.ne').mpr hs]
  rw [he, show Ring.multichoose (a + b + 1) n =
      Ring.multichoose (a + b) n * (a + b + n) / (a + b) from
        (eq_div_iff (add_pos ha hb).ne').mpr hn]
  field_simp [(multichoose_pos ha ij.1).ne', (multichoose_pos hb ij.2).ne',
    (multichoose_pos (add_pos ha hb) n).ne']

private theorem betaBinomial_normalized_log_le (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∑ ij ∈ HasAntidiagonal.antidiagonal n, betaBinomialMass ((a : ℝ) + 1) b n ij *
      Real.log (((a : ℝ) + ij.1) / ((a : ℝ) + b + n)) ≤
        -(∑ k ∈ range b, ((a : ℝ) + 1 + k)⁻¹) := by
  have h := betaBinomial_weighted_log_le (a + 1) b n (by omega) hb
  have hnum (k : ℕ) : ((a + 1 + k - 1 : ℕ) : ℝ) = (a : ℝ) + k := by
    rw [show a + 1 + k - 1 = a + k by omega, Nat.cast_add]
  have hden : ((a + 1 + b + n - 1 : ℕ) : ℝ) = (a : ℝ) + b + n := by
    rw [show a + 1 + b + n - 1 = a + b + n by omega]
    push_cast
    rfl
  simp only [hnum, hden, Nat.cast_succ] at h
  have hn : 0 < Ring.multichoose ((a : ℝ) + 1 + b) n :=
    multichoose_pos (by positivity) n
  calc
    _ = (∑ ij ∈ HasAntidiagonal.antidiagonal n,
        Ring.multichoose ((a : ℝ) + 1) ij.1 * Ring.multichoose (b : ℝ) ij.2 *
          Real.log (((a : ℝ) + ij.1) / ((a : ℝ) + b + n))) /
        Ring.multichoose ((a : ℝ) + 1 + b) n := by
      simp only [betaBinomialMass, div_eq_mul_inv, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ ≤ _ := (div_le_iff₀ hn).mpr (by simpa only [mul_neg, neg_mul, mul_comm] using h)

/-- The exact likelihood ratio and harmonic bound control the entropy cost
of increasing one parameter by one. The estimate is uniform in the sample size. -/
theorem betaBinomial_relativeEntropy_shift_le (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∑ ij ∈ HasAntidiagonal.antidiagonal n, betaBinomialMass ((a : ℝ) + 1) b n ij *
      Real.log (betaBinomialMass ((a : ℝ) + 1) b n ij / betaBinomialMass a b n ij) ≤
      Real.log (((a : ℝ) + b) / a) - ∑ k ∈ range b, ((a : ℝ) + 1 + k)⁻¹ := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hpoint (ij : ℕ × ℕ) :
      Real.log (betaBinomialMass ((a : ℝ) + 1) b n ij / betaBinomialMass a b n ij) =
        Real.log (((a : ℝ) + b) / a) +
          Real.log (((a : ℝ) + ij.1) / ((a : ℝ) + b + n)) := by
    rw [betaBinomialMass_ratio_shift ha' hb', Real.log_mul (by positivity) (by positivity)]
  simp_rw [hpoint, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_betaBinomialMass (by positivity : 0 < (a : ℝ) + 1) hb' n, one_mul]
  rw [sub_eq_add_neg]
  exact add_le_add_right (betaBinomial_normalized_log_le a b n ha hb) _

/-- Increasing the parameter by two costs at most two copies of the
harmonic bound evaluated under the final law. -/
theorem betaBinomial_relativeEntropy_shift_two_le (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∑ ij ∈ HasAntidiagonal.antidiagonal n, betaBinomialMass ((a : ℝ) + 2) b n ij *
      Real.log (betaBinomialMass ((a : ℝ) + 2) b n ij / betaBinomialMass a b n ij) ≤
      Real.log (((a : ℝ) + b) / a) + Real.log (((a : ℝ) + 1 + b) / (a + 1)) -
        2 * ∑ k ∈ range b, ((a : ℝ) + 2 + k)⁻¹ := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  let constant := Real.log (((a : ℝ) + b) / a) +
    Real.log (((a : ℝ) + 1 + b) / (a + 1))
  let logarithm (i : ℕ) := Real.log (((a : ℝ) + 1 + i) / ((a : ℝ) + 1 + b + n))
  have hpoint (ij : ℕ × ℕ) (hij : ij ∈ HasAntidiagonal.antidiagonal n) :
      Real.log (betaBinomialMass ((a : ℝ) + 2) b n ij / betaBinomialMass a b n ij) ≤
        constant + 2 * logarithm ij.1 := by
    have hm := betaBinomialMass_pos (show 0 < (a : ℝ) + 1 by positivity) hb' n ij
    have htwo : (a : ℝ) + 2 = (a : ℝ) + 1 + 1 := by ring
    have hratio := betaBinomialMass_ratio_shift ha' hb' n ij
    have hratio' := betaBinomialMass_ratio_shift
      (show 0 < (a : ℝ) + 1 by positivity) hb' n ij
    rw [← htwo] at hratio'
    rw [show betaBinomialMass ((a : ℝ) + 2) b n ij / betaBinomialMass a b n ij =
      (betaBinomialMass ((a : ℝ) + 2) b n ij / betaBinomialMass ((a : ℝ) + 1) b n ij) *
        (betaBinomialMass ((a : ℝ) + 1) b n ij / betaBinomialMass a b n ij) by
        field_simp [hm.ne'], hratio', hratio]
    repeat rw [Real.log_mul (by positivity) (by positivity)]
    have hi : ij.1 ≤ n := HasAntidiagonal.antidiagonal.fst_le hij
    have hi' : (ij.1 : ℝ) ≤ n := by exact_mod_cast hi
    have hlog : Real.log (((a : ℝ) + ij.1) / ((a : ℝ) + b + n)) ≤ logarithm ij.1 := by
      apply Real.log_le_log (by positivity)
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [hi', hb']
    dsimp only [constant, logarithm]
    linarith only [hlog]
  have hlog := betaBinomial_normalized_log_le (a + 1) b n (by omega) hb
  rw [Nat.cast_succ, show (a : ℝ) + 1 + 1 = (a : ℝ) + 2 by ring] at hlog
  have hlog' : ∑ ij ∈ HasAntidiagonal.antidiagonal n, betaBinomialMass ((a : ℝ) + 2) b n ij *
      logarithm ij.1 ≤ -(∑ k ∈ range b, ((a : ℝ) + 2 + k)⁻¹) := by
    simpa [logarithm] using hlog
  calc
    _ ≤ ∑ ij ∈ HasAntidiagonal.antidiagonal n, betaBinomialMass ((a : ℝ) + 2) b n ij *
        (constant + 2 * logarithm ij.1) := by
      exact Finset.sum_le_sum fun ij hij ↦ mul_le_mul_of_nonneg_left (hpoint ij hij)
        (betaBinomialMass_pos (by positivity) hb' n ij).le
    _ = constant + 2 * ∑ ij ∈ HasAntidiagonal.antidiagonal n,
        betaBinomialMass ((a : ℝ) + 2) b n ij * logarithm ij.1 := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        sum_betaBinomialMass (by positivity : 0 < (a : ℝ) + 2) hb' n, one_mul]
      simp only [mul_left_comm _ (2 : ℝ), ← Finset.mul_sum]
    _ ≤ _ := by
      dsimp only [constant]
      linarith only [hlog']

private theorem multichoose_succ_mul (a : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * Ring.multichoose a (k + 1) = a * Ring.multichoose (a + 1) k := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hf : 0 < (k.factorial : ℝ) := by positivity
  simp only [multichoose_eq_prod, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
    Finset.prod_range_succ']
  have h : (∏ j ∈ range k, (a + ((j : ℝ) + 1))) =
      ∏ j ∈ range k, (a + 1 + (j : ℝ)) := by
    refine Finset.prod_congr rfl fun _ _ ↦ ?_
    ring
  rw [h]
  simp only [Nat.cast_zero, add_zero]
  field_simp [hk.ne', hf.ne']

/-- The first mean of the beta-binomial count, obtained without integration. -/
theorem betaBinomial_mean {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∑ ij ∈ HasAntidiagonal.antidiagonal n, betaBinomialMass a b n ij * (ij.1 : ℝ) =
      (n : ℝ) * a / (a + b) := by
  cases n with
  | zero => simp
  | succ n =>
    have hnorm := multichoose_pos (add_pos ha hb) (n + 1)
    have hsum : ∑ ij ∈ HasAntidiagonal.antidiagonal (n + 1),
        Ring.multichoose a ij.1 * Ring.multichoose b ij.2 * (ij.1 : ℝ) =
        a * Ring.multichoose (a + b + 1) n := by
      rw [Finset.Nat.sum_antidiagonal_succ]
      simp only [Nat.cast_zero, mul_zero, zero_add, Nat.cast_succ]
      have hs (k l : ℕ) :
          Ring.multichoose a (k + 1) * Ring.multichoose b l * ((k : ℝ) + 1) =
            a * (Ring.multichoose (a + 1) k * Ring.multichoose b l) := by
        linear_combination Ring.multichoose b l * multichoose_succ_mul a k
      simp only [hs, ← Finset.mul_sum, ← multichoose_add,
        show a + 1 + b = a + b + 1 by ring]
    calc
      _ = (∑ ij ∈ HasAntidiagonal.antidiagonal (n + 1),
          Ring.multichoose a ij.1 * Ring.multichoose b ij.2 * (ij.1 : ℝ)) /
          Ring.multichoose (a + b) (n + 1) := by
        simp only [betaBinomialMass, div_eq_mul_inv, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ = _ := by
        rw [hsum, Nat.cast_succ]
        field_simp [hnorm.ne', (add_pos ha hb).ne']
        linear_combination -multichoose_succ_mul (a + b) n


/-- A beta-binomial moment at any real argument has a lower bound from the
mean and relative entropy of another beta-binomial law of the same size. -/
theorem betaBinomial_moment_lower {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (n : ℕ) (t entropy : ℝ)
    (hentropy : ∑ ij ∈ HasAntidiagonal.antidiagonal n, betaBinomialMass c d n ij *
        Real.log (betaBinomialMass c d n ij / betaBinomialMass a b n ij) ≤ entropy) :
    Real.exp (t * ((n : ℝ) * c / (c + d)) - entropy) ≤
      ∑ ij ∈ HasAntidiagonal.antidiagonal n,
        betaBinomialMass a b n ij * Real.exp (t * ij.1) := by
  have hmean := betaBinomial_mean hc hd n
  have hj := convexOn_exp.map_sum_le (t := HasAntidiagonal.antidiagonal n)
    (w := betaBinomialMass c d n)
    (p := fun ij ↦ t * (ij.1 : ℝ) -
      Real.log (betaBinomialMass c d n ij / betaBinomialMass a b n ij))
    (fun ij _ ↦ (betaBinomialMass_pos hc hd n ij).le)
    (sum_betaBinomialMass hc hd n) (fun _ _ ↦ Set.mem_univ _)
  simp only [smul_eq_mul, mul_sub, Finset.sum_sub_distrib] at hj
  have h₁ : (∑ ij ∈ HasAntidiagonal.antidiagonal n,
      betaBinomialMass c d n ij * (t * (ij.1 : ℝ))) =
      t * ((n : ℝ) * c / (c + d)) := by
    rw [← hmean, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [h₁] at hj
  refine (Real.exp_le_exp.mpr (sub_le_sub_left hentropy _)).trans (hj.trans_eq ?_)
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [Real.exp_sub, Real.exp_log (div_pos (betaBinomialMass_pos hc hd n ij)
    (betaBinomialMass_pos ha hb n ij))]
  field_simp [(betaBinomialMass_pos hc hd n ij).ne', (betaBinomialMass_pos ha hb n ij).ne']


private theorem betaBinomialMass_swap (a b : ℝ) (n : ℕ) (ij : ℕ × ℕ) :
    betaBinomialMass a b n ij.swap = betaBinomialMass b a n ij := by
  simp only [betaBinomialMass, Prod.fst_swap, Prod.snd_swap, mul_comm, add_comm]

private theorem betaBinomial_entropy_swap (a b c d : ℝ) (n : ℕ) :
    (∑ ij ∈ HasAntidiagonal.antidiagonal n, betaBinomialMass a b n ij *
      Real.log (betaBinomialMass a b n ij / betaBinomialMass c d n ij)) =
    ∑ ij ∈ HasAntidiagonal.antidiagonal n, betaBinomialMass b a n ij *
      Real.log (betaBinomialMass b a n ij / betaBinomialMass d c n ij) := by
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp only [betaBinomialMass_swap]

private def entropy13 : ℝ := Real.log (3 / 2) - 1 / 3
private def entropy22 : ℝ := Real.log 3 - 5 / 6
private def entropy26 : ℝ := Real.log (21 / 10) - 13 / 21

private theorem entropy13_le_entropy22 : entropy13 ≤ entropy22 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ)⁻¹)
  rw [Real.log_inv] at h
  unfold entropy13 entropy22
  rw [Real.log_div (by norm_num) (by norm_num)]
  norm_num at h
  linarith only [h]

private theorem combined_entropy_le :
    (entropy13 + 3 * entropy22) / 2 + entropy26 ≤ Real.log (9 / 5) := by
  have hlow : (441 : ℝ) / 8 ≤ Real.exp (57 / 14) := by
    have h := Real.sum_le_exp_of_nonneg (x := (57 : ℝ) / 14) (by norm_num) 8
    have hsum : (441 : ℝ) / 8 ≤ ∑ i ∈ range 8, ((57 : ℝ) / 14) ^ i / i.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hsum.trans h
  have hlog := (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 441 / 8)).mpr hlow
  have hrewrite : Real.log (441 / 8 : ℝ) =
      Real.log (3 / 2) + 3 * Real.log 3 + 2 * Real.log (21 / 10) - 2 * Real.log (9 / 5) := by
    have heq : (441 / 8 : ℝ) =
        ((3 / 2) * 3 ^ (3 : ℕ) * ((21 : ℝ) / 10) ^ (2 : ℕ)) / ((9 : ℝ) / 5) ^ (2 : ℕ) :=
      by norm_num
    rw [heq, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow, Nat.cast_ofNat]
  rw [hrewrite] at hlog
  unfold entropy13 entropy22 entropy26
  linarith only [hlog]

private theorem beta_exp_lower_13 (n : ℕ) (t : ℝ) :
    Real.exp (t * ((n : ℝ) / 4) - entropy13) ≤
      ∑ ij ∈ HasAntidiagonal.antidiagonal n,
        betaBinomialMass 1 2 n ij * Real.exp (t * ij.1) := by
  have h := betaBinomial_relativeEntropy_shift_le 2 1 n (by decide) (by decide)
  norm_num [entropy13, Finset.sum_range_succ] at h
  have he : ∑ ij ∈ HasAntidiagonal.antidiagonal n, betaBinomialMass 1 3 n ij *
      Real.log (betaBinomialMass 1 3 n ij / betaBinomialMass 1 2 n ij) ≤ entropy13 := by
    rw [betaBinomial_entropy_swap]
    exact h
  simpa only [mul_one, show (1 : ℝ) + 3 = 4 by norm_num] using
    betaBinomial_moment_lower (a := 1) (b := 2) (c := 1) (d := 3)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) n t entropy13 he

private theorem beta_exp_lower_22 (n : ℕ) (t : ℝ) :
    Real.exp (t * ((n : ℝ) / 2) - entropy22) ≤
      ∑ ij ∈ HasAntidiagonal.antidiagonal n,
        betaBinomialMass 1 2 n ij * Real.exp (t * ij.1) := by
  have h := betaBinomial_relativeEntropy_shift_le 1 2 n (by decide) (by decide)
  norm_num [entropy22, Finset.sum_range_succ] at h
  have he := betaBinomial_moment_lower (a := 1) (b := 2) (c := 2) (d := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) n t entropy22 h
  convert he using 2
  ring

private theorem beta_exp_lower_26 (n : ℕ) (t : ℝ) :
    Real.exp (t * ((n : ℝ) / 4) - entropy26) ≤
      ∑ ij ∈ HasAntidiagonal.antidiagonal n,
        betaBinomialMass 2 4 n ij * Real.exp (t * ij.1) := by
  have h := betaBinomial_relativeEntropy_shift_two_le 4 2 n (by decide) (by decide)
  have he : ∑ ij ∈ HasAntidiagonal.antidiagonal n, betaBinomialMass 2 6 n ij *
      Real.log (betaBinomialMass 2 6 n ij / betaBinomialMass 2 4 n ij) ≤ entropy26 := by
    rw [betaBinomial_entropy_swap]
    have hlog : Real.log (21 / 10 : ℝ) = Real.log (3 / 2) + Real.log (7 / 5) := by
      rw [show (21 / 10 : ℝ) = (3 / 2) * (7 / 5) by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    norm_num [Finset.sum_range_succ] at h
    unfold entropy26
    rw [hlog]
    linarith only [h]
  have hmoment := betaBinomial_moment_lower (a := 2) (b := 4) (c := 2) (d := 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) n t entropy26 he
  convert hmoment using 2
  ring


/-- The product of the three normalized exponential moments overcomes the
centering loss of a four-cycle with one zero label, uniformly in the degree. -/
theorem one_zero_betaBinomial_moment_product (p : ℕ) (hp : 2 ≤ p) (x y : ℝ) :
    let f (t : ℝ) := ∑ ij ∈ HasAntidiagonal.antidiagonal p,
      betaBinomialMass 1 2 p ij * Real.exp (t * ij.1)
    let g (t : ℝ) := ∑ ij ∈ HasAntidiagonal.antidiagonal (p - 1),
      betaBinomialMass 2 4 (p - 1) ij * Real.exp (t * ij.1)
    Real.exp ((p : ℝ) * y - Real.log (9 / 5)) ≤ f (y - x) * f (y + x) * g (y - x) := by
  intro f g
  let w : ℝ := (p : ℝ)⁻¹
  have hp' : 2 ≤ (p : ℝ) := by exact_mod_cast hp
  have hp₀ : 0 < (p : ℝ) := by positivity
  have hw₀ : 0 ≤ w := inv_nonneg.mpr hp₀.le
  have hw : w ≤ 1 / 2 := by
    dsimp [w]
    rw [inv_eq_one_div]
    exact (div_le_div_iff₀ hp₀ (by norm_num)).mpr (by simpa only [one_mul] using hp')
  have hleft₀ : 0 < f (y - x) := (Real.exp_pos _).trans_le (beta_exp_lower_13 p (y - x))
  have hright₀ : 0 < f (y + x) := (Real.exp_pos _).trans_le (beta_exp_lower_22 p (y + x))
  have hthird₀ : 0 < g (y - x) := (Real.exp_pos _).trans_le (beta_exp_lower_26 (p - 1) (y - x))
  have hleft₁ := (Real.le_log_iff_exp_le hleft₀).mpr (beta_exp_lower_13 p (y - x))
  have hleft₂ := (Real.le_log_iff_exp_le hleft₀).mpr (beta_exp_lower_22 p (y - x))
  have hright := (Real.le_log_iff_exp_le hright₀).mpr (beta_exp_lower_22 p (y + x))
  have hthird := (Real.le_log_iff_exp_le hthird₀).mpr (beta_exp_lower_26 (p - 1) (y - x))
  have hmean : (1 - w) * ((y - x) * ((p : ℝ) / 4)) + w * ((y - x) * ((p : ℝ) / 2)) =
      (y - x) * (((p : ℝ) + 1) / 4) := by
    dsimp [w]
    field_simp [hp₀.ne']
    ring
  have hleft : (y - x) * (((p : ℝ) + 1) / 4) -
      ((1 - w) * entropy13 + w * entropy22) ≤ Real.log (f (y - x)) := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hleft₁ (show 0 ≤ 1 - w by linarith))
      (mul_le_mul_of_nonneg_left hleft₂ hw₀)
    rw [← add_mul, sub_add_cancel, one_mul, mul_sub, mul_sub] at h
    linarith only [h, hmean]
  have hcost : (1 - w) * entropy13 + w * entropy22 + entropy22 + entropy26 ≤
      Real.log (9 / 5) := by
    have h := mul_le_mul_of_nonneg_right hw (sub_nonneg.mpr entropy13_le_entropy22)
    linarith only [h, combined_entropy_le]
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at hthird
  apply (Real.le_log_iff_exp_le (mul_pos (mul_pos hleft₀ hright₀) hthird₀)).mp
  rw [Real.log_mul (mul_ne_zero hleft₀.ne' hright₀.ne') hthird₀.ne',
    Real.log_mul hleft₀.ne' hright₀.ne']
  linarith only [hleft, hright, hthird, hcost]


private theorem multichoose_two (n : ℕ) :
    Ring.multichoose (2 : ℝ) n = (n : ℝ) + 1 := by
  have h := multichoose_add_one_mul 1 n
  norm_num [Ring.multichoose_one, add_comm] at h
  exact h

private theorem multichoose_three (n : ℕ) :
    Ring.multichoose (3 : ℝ) n = ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by
  have h := multichoose_add_one_mul 2 n
  norm_num [multichoose_two] at h
  linear_combination h / 2

private theorem multichoose_four (n : ℕ) :
    Ring.multichoose (4 : ℝ) n = ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) / 6 := by
  have h := multichoose_add_one_mul 3 n
  norm_num [multichoose_three] at h
  linear_combination h / 3

private theorem multichoose_five (n : ℕ) :
    Ring.multichoose (5 : ℝ) n =
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) / 24 := by
  have h := multichoose_add_one_mul 4 n
  norm_num [multichoose_four] at h
  linear_combination h / 4

private theorem multichoose_six (n : ℕ) :
    Ring.multichoose (6 : ℝ) n =
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) *
        ((n : ℝ) + 4) * ((n : ℝ) + 5) / 120 := by
  have h := multichoose_add_one_mul 5 n
  norm_num [multichoose_five] at h
  linear_combination h / 5

theorem betaBinomial_12_exp_eq (p : ℕ) (t : ℝ) :
    ∑ ij ∈ HasAntidiagonal.antidiagonal p, betaBinomialMass 1 2 p ij * Real.exp (t * ij.1) =
      (∑ k ∈ range (p + 1), (((p - k : ℕ) : ℝ) + 1) * Real.exp t ^ k) /
        (((p : ℝ) + 1) * ((p : ℝ) + 2) / 2) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  unfold betaBinomialMass
  simp only [show (1 : ℝ) + 2 = 3 by norm_num, Ring.multichoose_one, multichoose_two,
    multichoose_three, one_mul, mul_comm t, Real.exp_nat_mul, div_eq_mul_inv]
  ring

theorem betaBinomial_24_exp_eq {p : ℕ} (hp : 0 < p) (t : ℝ) :
    ∑ ij ∈ HasAntidiagonal.antidiagonal (p - 1), betaBinomialMass 2 4 (p - 1) ij *
        Real.exp (t * ij.1) =
      (∑ k ∈ range (p + 1),
        let j : ℝ := (p - k : ℕ)
        (((k : ℝ) + 1) * (j + 1) * j * (j + 2) /
          (((p : ℝ) + 1) * (p : ℝ) * ((p : ℝ) + 2))) * Real.exp t ^ k) /
        (((p : ℝ) + 3) * ((p : ℝ) + 4) / 20) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, show (p - 1).succ = p by omega,
    Finset.sum_range_succ]
  simp only [Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k < p := Finset.mem_range.mp hk
  have he : p - 1 - k = (p - k) - 1 := by omega
  have hj : 1 ≤ p - k := by omega
  unfold betaBinomialMass
  simp only [show (2 : ℝ) + 4 = 6 by norm_num, multichoose_two, multichoose_four,
    multichoose_six, mul_comm t, Real.exp_nat_mul]
  rw [he, Nat.cast_sub hj, Nat.cast_sub (by omega : 1 ≤ p)]
  simp only [Nat.cast_one, sub_add_cancel,
    show ∀ r : ℝ, r - 1 + 2 = r + 1 by intro r; ring,
    show ∀ r : ℝ, r - 1 + 3 = r + 2 by intro r; ring,
    show ∀ r : ℝ, r - 1 + 4 = r + 3 by intro r; ring,
    show ∀ r : ℝ, r - 1 + 5 = r + 4 by intro r; ring]
  field_simp [hpR.ne', show (p : ℝ) + 1 ≠ 0 by positivity,
    show (p : ℝ) + 2 ≠ 0 by positivity,
    show (p : ℝ) + 3 ≠ 0 by positivity, show (p : ℝ) + 4 ≠ 0 by positivity]
  ring


/-- The unnormalized moment product dominates the square of the balanced
composition term on the one-zero face. -/
theorem one_zero_polynomial_moment_product (p : ℕ) (hp : 2 ≤ p) (x y : ℝ) :
    let f (t : ℝ) := ∑ k ∈ range (p + 1), (((p - k : ℕ) : ℝ) + 1) * t ^ k
    let g (t : ℝ) := ∑ k ∈ range (p + 1),
      let j : ℝ := (p - k : ℕ)
      (((k : ℝ) + 1) * (j + 1) * j * (j + 2) /
        (((p : ℝ) + 1) * (p : ℝ) * ((p : ℝ) + 2))) * t ^ k
    (((p : ℝ) + 1) * ((p : ℝ) + 2) * ((p : ℝ) + 3) / 6) ^ 2 *
        Real.exp ((p : ℝ) * y) ≤
      4 * (f (Real.exp (y - x)) * f (Real.exp (y + x))) * g (Real.exp (y - x)) := by
  intro f g
  let denomF : ℝ := ((p : ℝ) + 1) * ((p : ℝ) + 2) / 2
  let denomG : ℝ := ((p : ℝ) + 3) * ((p : ℝ) + 4) / 20
  have hF : 0 < denomF := by dsimp [denomF]; positivity
  have hG : 0 < denomG := by dsimp [denomG]; positivity
  have hn := one_zero_betaBinomial_moment_product p hp x y
  dsimp only at hn
  rw [betaBinomial_12_exp_eq, betaBinomial_12_exp_eq,
    betaBinomial_24_exp_eq (show 0 < p by omega), Real.exp_sub, Real.exp_log (by norm_num)] at hn
  change Real.exp ((p : ℝ) * y) / (9 / 5) ≤
      (f (Real.exp (y - x)) / denomF) * (f (Real.exp (y + x)) / denomF) *
        (g (Real.exp (y - x)) / denomG) at hn
  have hm := mul_le_mul_of_nonneg_right hn (show 0 ≤ denomF * denomF * denomG by positivity)
  have hprod : (f (Real.exp (y - x)) / denomF) * (f (Real.exp (y + x)) / denomF) *
        (g (Real.exp (y - x)) / denomG) * (denomF * denomF * denomG) =
      (f (Real.exp (y - x)) * f (Real.exp (y + x))) * g (Real.exp (y - x)) := by
    field_simp [hF.ne', hG.ne']
  rw [hprod] at hm
  have hcoef : (((p : ℝ) + 1) * ((p : ℝ) + 2) * ((p : ℝ) + 3) / 6) ^ 2 ≤
        4 * (denomF * denomF * denomG) / (9 / 5) := by
    have heq : 4 * (denomF * denomF * denomG) / (9 / 5) -
        (((p : ℝ) + 1) * ((p : ℝ) + 2) * ((p : ℝ) + 3) / 6) ^ 2 =
      (((p : ℝ) + 1) * ((p : ℝ) + 2)) ^ 2 * ((p : ℝ) + 3) / 36 := by
      dsimp only [denomF, denomG]
      ring
    have hnon : 0 ≤ (((p : ℝ) + 1) * ((p : ℝ) + 2)) ^ 2 * ((p : ℝ) + 3) / 36 := by
      positivity
    linarith only [heq, hnon]
  have he := mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg ((p : ℝ) * y))
  linarith only [he, hm]

#print axioms betaBinomial_harmonic_expectation
#print axioms betaBinomial_weighted_log_le
#print axioms betaBinomial_relativeEntropy_shift_le
#print axioms betaBinomial_relativeEntropy_shift_two_le
#print axioms betaBinomial_mean
#print axioms betaBinomial_moment_lower
#print axioms one_zero_betaBinomial_moment_product
#print axioms betaBinomial_12_exp_eq
#print axioms betaBinomial_24_exp_eq
#print axioms one_zero_polynomial_moment_product

end

end RefinedBMV.Tracial
