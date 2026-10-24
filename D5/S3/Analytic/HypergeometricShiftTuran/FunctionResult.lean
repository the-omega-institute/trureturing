/- GID: D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult
   generality: G
   mirror-B: D5/B/S3/Analytic/HypergeometricShiftTuran/FunctionResult
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.claim; result=D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.result; claim=D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.claim
   digest: A convergent Gamma-series counterexample to function nonnegativity in Conjecture 1. -/

import D5.S3.Analytic.HypergeometricShiftTuran.Defs

/-! A function-level refutation using convergent positive Gamma series. -/

noncomputable section
open scoped BigOperators
open D5.S3.Analytic.HypergeometricShiftTuran.Defs
open Filter

namespace D5.S3.Analytic.HypergeometricShiftTuran.FunctionResult

/-- The series in equation (10), interpreted as a real infinite sum. -/
def fval {p q : ℕ} (a : Fin p → ℝ) (b : Fin q → ℝ) (μ x : ℝ) : ℝ :=
  ∑' n : ℕ, coeff a b (μ + n) * x ^ n / (n.factorial : ℝ)

/-- The function Turanian in equation (9). -/
def turanian {p q : ℕ} (a : Fin p → ℝ) (b : Fin q → ℝ) (μ α β x : ℝ) : ℝ :=
  fval a b (μ + α) x * fval a b (μ + β) x -
    fval a b μ x * fval a b (μ + α + β) x

/-- The function nonnegativity clause of Conjecture 1. -/
def claim : Prop :=
  ∀ (p q : ℕ) (a : Fin p → ℝ) (b : Fin q → ℝ),
    p ≤ q → (∀ i, 0 < a i) → (∀ j, 0 < b j) → cond13 a b →
      ∀ μ α β x : ℝ, 1 ≤ μ → 0 ≤ α → 0 ≤ β → 0 ≤ x →
        0 ≤ turanian a b μ α β x

private def term (t : ℝ) (n : ℕ) : ℝ :=
  (Real.Gamma (t + n))⁻¹ ^ 12 * 5000 ^ n / (n.factorial : ℝ)
private lemma term_nonneg (t : ℝ) (n : ℕ) : 0 ≤ term t n := by
  unfold term
  positivity
private lemma term_step (t : ℝ) (ht : 0 < t) (n : ℕ) :
    term t (n+1) = (5000 / (((n : ℝ)+1) * (t+n)^12)) * term t n := by
  have htn : t + (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
  unfold term
  rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Real.Gamma_add_one htn,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  simp only [mul_inv_rev, mul_pow]
  field_simp
  ring
private lemma term_ratio (t : ℝ) (ht : 1 ≤ t) (n : ℕ) (hn : 8 ≤ n) :
    term t (n+1) ≤ (1/2:ℝ) * term t n := by
  rw [term_step t (by linarith) n]
  apply mul_le_mul_of_nonneg_right _ (term_nonneg t n)
  have hn' : (8 : ℝ) ≤ n := Nat.ofNat_le_cast.mpr hn
  have hp : (9 : ℝ)^12 ≤ (t+n)^12 := pow_le_pow_left₀ (Nat.ofNat_nonneg' 9) (by linarith) 12
  apply (div_le_iff₀ (by positivity : 0 < ((n:ℝ)+1)*(t+n)^12)).2
  nlinarith
private lemma term_summable (t : ℝ) (ht : 1 ≤ t) : Summable (term t) := by
  apply summable_of_ratio_norm_eventually_le one_half_lt_one
  filter_upwards [eventually_ge_atTop 8] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (term_nonneg t _)] using term_ratio t ht n hn

private def aterm (n : ℕ) : ℝ :=
  5000 ^ n / ((n.factorial : ℝ) * ((n+1).factorial : ℝ)^12)

private def hterm (k n : ℕ) : ℝ :=
  5000 ^ n / ((n.factorial : ℝ) *
    (((2*(n+k)-1).doubleFactorial : ℝ) / 2^(n+k))^12)

private lemma term_integer (n : ℕ) : term 2 n = aterm n := by
  unfold term aterm
  rw [show (2:ℝ)+n = ((n+1 : ℕ):ℝ)+1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]
  simp only [inv_pow, div_eq_mul_inv, mul_inv_rev]
  ring

private lemma term_half (k n : ℕ) :
    term ((k:ℝ)+1/2) n = Real.pi⁻¹^6 * hterm k n := by
  have hs : (Real.sqrt Real.pi)^12 = Real.pi^6 := by
    rw [show 12 = 2*6 from (Nat.succ_mul_succ 1 5).symm, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  unfold term hterm
  rw [show (k:ℝ)+1/2+n = ((n+k:ℕ):ℝ)+1/2 by push_cast; ring,
    Real.Gamma_nat_add_half]
  rw [inv_pow, div_pow, mul_pow, hs]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv]
  ring_nf
  norm_num

private def rho : ℝ := 5000 / (9 * 10^12)

private lemma aterm_ratio (n : ℕ) (hn : 8 ≤ n) :
    term 2 (n+1) ≤ rho * term 2 n := by
  rw [term_step 2 zero_lt_two n]
  apply mul_le_mul_of_nonneg_right _ (term_nonneg 2 n)
  have hn' : (8:ℝ) ≤ n := Nat.ofNat_le_cast.mpr hn
  have hp : (10:ℝ)^12 ≤ (2+n)^12 := pow_le_pow_left₀ (Nat.ofNat_nonneg' 10) (by linarith) 12
  unfold rho
  apply div_le_div_of_nonneg_left (Nat.ofNat_nonneg' 5000) (by norm_num)
  nlinarith

private lemma aterm_upper :
    (∑' n, term 2 n) ≤ (∑ n ∈ Finset.range 8, aterm n) + aterm 8 / (1-rho) := by
  have hr0 : 0 ≤ rho := by norm_num [rho]
  have hr1 : rho < 1 := by norm_num [rho]
  have hm (n : ℕ) : term 2 (n+8) ≤ rho^n * term 2 8 := by
    simpa only [zero_add] using le_geom (u := fun n => term 2 (n+8)) hr0 n
      (fun k _ => aterm_ratio (k+8) (Nat.le_add_left 8 k))
  have htail := Summable.tsum_le_tsum hm
    ((summable_nat_add_iff 8).2 (term_summable 2 one_le_two))
    ((summable_geometric_of_lt_one hr0 hr1).mul_right (term 2 8))
  rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1, term_integer] at htail
  have he := Summable.sum_add_tsum_nat_add 8 (term_summable 2 one_le_two)
  simp_rw [term_integer] at he
  simp_rw [term_integer] at htail
  simp_rw [term_integer]
  rw [← he]
  exact add_le_add le_rfl (by simpa [div_eq_mul_inv, mul_comm] using htail)

private lemma aterm_upper_numeric :
    (∑ n ∈ Finset.range 8, aterm n) + aterm 8 / (1-rho) ≤ (9/4:ℝ) := by
  norm_num [aterm, rho, Finset.sum_range_succ, Nat.factorial]

private lemma hterm_lower (k : ℕ) :
    (∑ n ∈ Finset.range 2, hterm k n) ≤ ∑ n ∈ Finset.range 8, hterm k n := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono Nat.AtLeastTwo.prop)
  intro n _ _
  unfold hterm
  positivity

private lemma half_lower (k : ℕ) (hk : 1 ≤ k) :
    Real.pi⁻¹^6 * (∑ n ∈ Finset.range 8, hterm k n) ≤ ∑' n, term ((k:ℝ)+1/2) n := by
  have h := Summable.sum_le_tsum (Finset.range 8)
    (fun n _ => term_nonneg ((k:ℝ)+1/2) n)
    (term_summable ((k:ℝ)+1/2) (by
      have h : (1:ℝ) ≤ k := Nat.one_le_cast.mpr hk
      linarith))
  simpa only [term_half, Finset.mul_sum] using h

private lemma fval_eq (μ : ℝ) (hμ : 1 ≤ μ) :
    fval (fun _ : Fin 0 => 0) (fun _ : Fin 12 => (1/2:ℝ)) μ 5000 =
      ∑' n, term (μ+1/2) n := by
  unfold fval
  have hsum : HasSum (fun n : ℕ =>
      coeff (fun _ : Fin 0 => 0) (fun _ : Fin 12 => (1/2:ℝ)) (μ+n) *
        5000^n / (n.factorial : ℝ)) (∑' n, term (μ+1/2) n) := by
    convert (term_summable (μ+1/2) (by linarith)).hasSum using 1
    ext n
    simp [coeff, term, inv_pow, add_left_comm, add_assoc, add_comm]
  exact hsum.tsum_eq

private lemma witness_negative :
    turanian (fun _ : Fin 0 => 0) (fun _ : Fin 12 => (1/2:ℝ))
      1 (1/2) (1/2) 5000 < 0 := by
  have ha : (∑' n, term 2 n) ≤ (9/4:ℝ) := aterm_upper.trans aterm_upper_numeric
  have ha0 : 0 ≤ ∑' n, term 2 n := tsum_nonneg (term_nonneg 2)
  have hr : (161000:ℝ) ≤ ∑ n ∈ Finset.range 8, hterm 1 n := by
    refine le_trans ?_ (hterm_lower 1)
    norm_num [hterm, Finset.sum_range_succ, Nat.doubleFactorial]
  have hs : (34:ℝ) ≤ ∑ n ∈ Finset.range 8, hterm 2 n := by
    refine le_trans ?_ (hterm_lower 2)
    norm_num [hterm, Finset.sum_range_succ, Nat.doubleFactorial]
  have hr' : Real.pi⁻¹^6 * 161000 ≤ ∑' n, term (3/2) n := by
    exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans
      (by convert half_lower 1 NeZero.one_le using 1 <;> norm_num)
  have hs' : Real.pi⁻¹^6 * 34 ≤ ∑' n, term (5/2) n := by
    exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans
      (by convert half_lower 2 NeZero.one_le using 1 <;> norm_num)
  have hpi : (9/4:ℝ)^2 * Real.pi^12 < 161000*34 := by
    calc
      _ ≤ (9/4:ℝ)^2 * (3.1416:ℝ)^12 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d4.le 12) (sq_nonneg (9/4))
      _ < _ := by norm_num
  have hnum : (9/4:ℝ)^2 < (Real.pi⁻¹^6 * 161000) * (Real.pi⁻¹^6 * 34) := by
    have he : (Real.pi⁻¹^6 * 161000) * (Real.pi⁻¹^6 * 34) =
        (161000*34:ℝ) / Real.pi^12 := by
      field_simp
    rw [he]
    exact (lt_div_iff₀ (by positivity)).2 hpi
  have hprod := mul_le_mul hr' hs' (by positivity : 0 ≤ Real.pi⁻¹^6 * 34)
    (tsum_nonneg (term_nonneg (3/2)))
  have hmid := mul_self_le_mul_self ha0 ha
  unfold turanian
  norm_num only
  simp only [fval_eq (3/2) (by norm_num), fval_eq 1 (le_refl 1),
    fval_eq 2 one_le_two]
  norm_num only at *
  nlinarith

/-- Conjecture 1's universal function nonnegativity assertion is false. -/
theorem result : ¬ claim := by
  intro hclaim
  have h := hclaim 0 12 (fun _ : Fin 0 => 0) (fun _ : Fin 12 => (1/2:ℝ))
    (Nat.zero_le 12) (by intro i; exact Fin.elim0 i) (fun _ => one_half_pos)
    (by intro j hj; exact (Nat.not_lt_zero j hj).elim)
    1 (1/2) (1/2) 5000 (le_refl 1) (by norm_num) (by norm_num)
    (Nat.ofNat_nonneg' 5000)
  exact (not_lt_of_ge h) witness_negative

end D5.S3.Analytic.HypergeometricShiftTuran.FunctionResult
