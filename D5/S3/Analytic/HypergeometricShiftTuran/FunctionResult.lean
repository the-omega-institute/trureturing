/- GID: D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult
   generality: G
   mirror-B: D5/B/S3/Analytic/HypergeometricShiftTuran/FunctionResult
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.claim; result=D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.result; claim=D5/S3/Analytic/HypergeometricShiftTuran/FunctionResult.claim
   digest: A convergent Gamma-series counterexample to function nonnegativity in Conjecture 1. -/

/-
# Function nonnegativity fails for a convergent Gamma series

admission_basis: open-problem-resolution (#21189; Refuted)
All rows have proof_shape: bind-only and escape_witness: none.
Gamma recurrences, summability, geometric domination and the finite comparison
use pinned Mathlib instantiation and normalization. The external conjecture
settlement supplies the module's admission basis. The utility kind is
certified-instance with basis refutes; claim is the universal assertion and
result is its kernel-checked negation.
Declaration identities come from the scoped Lean producing report at
.lake/build/stratalint/scoped-lean-report.json.
Per-declaration judgement (compiled-value dependencies; new helpers inlined):
* fval: proof_shape: bind-only; escape_witness: none.
  consumers: fval_eq, turanian, witness_negative.
  direct frozen D5 dependencies:
    D5/S3/Analytic/HypergeometricShiftTuran/Defs.coeff;
      statement_id=sha256:0ed75eb9ee5b77546f2e79184697ab562a24a96cfe27b057ffe9cb70c1eb21f9.
* turanian: proof_shape: bind-only; escape_witness: none.
  consumers: claim, result, witness_negative.
  direct frozen D5 dependencies:
    D5/S3/Analytic/HypergeometricShiftTuran/Defs.coeff;
      statement_id=sha256:0ed75eb9ee5b77546f2e79184697ab562a24a96cfe27b057ffe9cb70c1eb21f9.
* claim: proof_shape: bind-only; escape_witness: none.
  consumers: result.
  direct frozen D5 dependencies:
    D5/S3/Analytic/HypergeometricShiftTuran/Defs.coeff;
      statement_id=sha256:0ed75eb9ee5b77546f2e79184697ab562a24a96cfe27b057ffe9cb70c1eb21f9.
    D5/S3/Analytic/HypergeometricShiftTuran/Defs.cond13;
      statement_id=sha256:08256b9ba6de16b5aa66622ef958a49cb8be4a4a907921a8d68019d0d20fa4c1.
* term: proof_shape: bind-only; escape_witness: none.
  consumers: aterm_ratio, aterm_upper, fval_eq, half_lower, term_half, term_integer,
    term_nonneg, term_ratio, term_step, term_summable, witness_negative.
  direct frozen D5 dependencies: none.
* term_nonneg: proof_shape: bind-only; escape_witness: none.
  consumers: aterm_ratio, half_lower, term_ratio, term_summable, witness_negative.
  direct frozen D5 dependencies: none.
* term_step: proof_shape: bind-only; escape_witness: none.
  consumers: aterm_ratio, term_ratio.
  direct frozen D5 dependencies: none.
* term_ratio: proof_shape: bind-only; escape_witness: none.
  consumers: term_summable.
  direct frozen D5 dependencies: none.
* term_summable: proof_shape: bind-only; escape_witness: none.
  consumers: aterm_upper, half_lower.
  direct frozen D5 dependencies: none.
* aterm: proof_shape: bind-only; escape_witness: none.
  consumers: aterm_upper, aterm_upper_numeric, term_integer, witness_negative.
  direct frozen D5 dependencies: none.
* hterm: proof_shape: bind-only; escape_witness: none.
  consumers: half_lower, hterm_lower, term_half, witness_negative.
  direct frozen D5 dependencies: none.
* term_integer: proof_shape: bind-only; escape_witness: none.
  consumers: aterm_upper.
  direct frozen D5 dependencies: none.
* term_half: proof_shape: bind-only; escape_witness: none.
  consumers: half_lower.
  direct frozen D5 dependencies: none.
* rho: proof_shape: bind-only; escape_witness: none.
  consumers: aterm_ratio, aterm_upper, aterm_upper_numeric, witness_negative.
  direct frozen D5 dependencies: none.
* aterm_ratio: proof_shape: bind-only; escape_witness: none.
  consumers: aterm_upper.
  direct frozen D5 dependencies: none.
* aterm_upper: proof_shape: bind-only; escape_witness: none.
  consumers: witness_negative.
  direct frozen D5 dependencies: none.
* aterm_upper_numeric: proof_shape: bind-only; escape_witness: none.
  consumers: witness_negative.
  direct frozen D5 dependencies: none.
* hterm_lower: proof_shape: bind-only; escape_witness: none.
  consumers: witness_negative.
  direct frozen D5 dependencies: none.
* half_lower: proof_shape: bind-only; escape_witness: none.
  consumers: witness_negative.
  direct frozen D5 dependencies: none.
* fval_eq: proof_shape: bind-only; escape_witness: none.
  consumers: witness_negative.
  direct frozen D5 dependencies:
    D5/S3/Analytic/HypergeometricShiftTuran/Defs.coeff;
      statement_id=sha256:0ed75eb9ee5b77546f2e79184697ab562a24a96cfe27b057ffe9cb70c1eb21f9.
* witness_negative: proof_shape: bind-only; escape_witness: none.
  consumers: result.
  direct frozen D5 dependencies:
    D5/S3/Analytic/HypergeometricShiftTuran/Defs.coeff;
      statement_id=sha256:0ed75eb9ee5b77546f2e79184697ab562a24a96cfe27b057ffe9cb70c1eb21f9.
* witness_cond13: proof_shape: bind-only; escape_witness: none.
  consumers: result.
  shared same-delivery helper: Defs.esymm_const (inlined below).
  direct frozen D5 dependencies:
    D5/S3/Analytic/HypergeometricShiftTuran/Defs.esymm;
      statement_id=sha256:4d8858460f0aad49d26a6547cf056cdd7fa4c7ed94938e4abfb0b427d2150a59.
* result: proof_shape: bind-only; escape_witness: none.
  consumers: external conjecture settlement #21189.
  direct frozen D5 dependencies:
    D5/S3/Analytic/HypergeometricShiftTuran/Defs.coeff;
      statement_id=sha256:0ed75eb9ee5b77546f2e79184697ab562a24a96cfe27b057ffe9cb70c1eb21f9.
    D5/S3/Analytic/HypergeometricShiftTuran/Defs.cond13;
      statement_id=sha256:08256b9ba6de16b5aa66622ef958a49cb8be4a4a907921a8d68019d0d20fa4c1.
    D5/S3/Analytic/HypergeometricShiftTuran/Defs.esymm;
      statement_id=sha256:4d8858460f0aad49d26a6547cf056cdd7fa4c7ed94938e4abfb0b427d2150a59.

The only public theorem is the refutation result, exempt under the utility
refutes rule. All proof helpers are private and have the named consumers.
-/

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
    1 ≤ p → p ≤ q → (∀ i, 0 < a i) → (∀ j, 0 < b j) → cond13 a b →
      ∀ μ α β x : ℝ, 1 ≤ μ → 0 ≤ α → 0 ≤ β → 0 ≤ x →
        0 ≤ turanian a b μ α β x

private def term (t : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma (t + 1/2 + n) * (Real.Gamma (t + n))⁻¹ ^ 12 *
    2000 ^ n / (n.factorial : ℝ)
private lemma term_nonneg (t : ℝ) (ht : 1 ≤ t) (n : ℕ) : 0 ≤ term t n := by
  unfold term
  have hg := (Real.Gamma_pos_of_pos (by positivity : 0 < t + 1/2 + (n:ℝ))).le
  positivity
private lemma term_step (t : ℝ) (ht : 0 < t) (n : ℕ) :
    term t (n+1) = (2000 * (t+1/2+n) / (((n : ℝ)+1) * (t+n)^12)) *
      term t n := by
  have htn : t + (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have htn' : t + 1/2 + (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
  unfold term
  rw [Nat.cast_add, Nat.cast_one, ← add_assoc, ← add_assoc,
    Real.Gamma_add_one htn', Real.Gamma_add_one htn,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  simp only [mul_inv_rev, mul_pow]
  field_simp
  ring
private lemma term_ratio (t : ℝ) (ht : 1 ≤ t) (n : ℕ) (hn : 8 ≤ n) :
    term t (n+1) ≤ (1/2:ℝ) * term t n := by
  rw [term_step t (by linarith) n]
  apply mul_le_mul_of_nonneg_right _ (term_nonneg t ht n)
  have hn' : (8 : ℝ) ≤ n := Nat.ofNat_le_cast.mpr hn
  have hu : (9:ℝ) ≤ t+n := by linarith
  have hp : (9 : ℝ)^11 ≤ (t+n)^11 := pow_le_pow_left₀ (by norm_num) hu 11
  have hp' : (9:ℝ)^11 * (t+n) ≤ (t+n)^12 := by
    simpa [pow_succ] using mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ t+n)
  apply (div_le_iff₀ (by positivity : 0 < ((n:ℝ)+1)*(t+n)^12)).2
  nlinarith
private lemma term_summable (t : ℝ) (ht : 1 ≤ t) : Summable (term t) := by
  apply summable_of_ratio_norm_eventually_le one_half_lt_one
  filter_upwards [eventually_ge_atTop 8] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (term_nonneg t ht _)] using term_ratio t ht n hn

private def aterm (n : ℕ) : ℝ :=
  (((2*(n+2)-1).doubleFactorial : ℝ) / 2^(n+2)) *
    2000 ^ n / ((n.factorial : ℝ) * ((n+1).factorial : ℝ)^12)

private def hterm (k n : ℕ) : ℝ :=
  ((n+k).factorial : ℝ) * 2000 ^ n / ((n.factorial : ℝ) *
    (((2*(n+k)-1).doubleFactorial : ℝ) / 2^(n+k))^12)

private lemma term_integer (n : ℕ) : term 2 n = Real.sqrt Real.pi * aterm n := by
  unfold term aterm
  rw [show (2:ℝ)+n = ((n+1 : ℕ):ℝ)+1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial,
    show (2:ℝ)+1/2+n = ((n+2:ℕ):ℝ)+1/2 by push_cast; ring,
    Real.Gamma_nat_add_half]
  simp only [inv_pow, div_eq_mul_inv, mul_inv_rev]
  ring

private lemma term_half (k n : ℕ) :
    term ((k:ℝ)+1/2) n = Real.pi⁻¹^6 * hterm k n := by
  have hs : (Real.sqrt Real.pi)^12 = Real.pi^6 := by
    rw [show 12 = 2*6 from (Nat.succ_mul_succ 1 5).symm, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  unfold term hterm
  rw [show (k:ℝ)+1/2+1/2+n = ((n+k:ℕ):ℝ)+1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial,
    show (k:ℝ)+1/2+n = ((n+k:ℕ):ℝ)+1/2 by push_cast; ring,
    Real.Gamma_nat_add_half]
  rw [inv_pow, div_pow, mul_pow, hs]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv]
  ring_nf
  norm_num

private def rho : ℝ := 74 / 100000000000

private lemma aterm_ratio (n : ℕ) (hn : 9 ≤ n) :
    term 2 (n+1) ≤ rho * term 2 n := by
  rw [term_step 2 zero_lt_two n]
  apply mul_le_mul_of_nonneg_right _ (term_nonneg 2 one_le_two n)
  have hn' : (9:ℝ) ≤ n := Nat.ofNat_le_cast.mpr hn
  have hp : (11:ℝ)^11 ≤ (2+n)^11 := pow_le_pow_left₀ (by norm_num) (by linarith) 11
  have hp' : (11:ℝ)^11 * (2+n) ≤ (2+n)^12 := by
    simpa [pow_succ] using mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ (2:ℝ)+n)
  apply (div_le_iff₀ (by positivity : 0 < ((n:ℝ)+1)*(2+n)^12)).2
  have hden : 10 * (11:ℝ)^11 * (2+n) ≤ ((n:ℝ)+1)*(2+n)^12 := by
    calc
      _ ≤ ((n:ℝ)+1) * ((11:ℝ)^11 * (2+n)) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hp' (by positivity)
  calc
    _ ≤ rho * (10 * (11:ℝ)^11 * (2+n)) := by
      norm_num [rho]
      nlinarith only [hn']
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by norm_num [rho])

private lemma aterm_upper :
    (∑' n, term 2 n) ≤ Real.sqrt Real.pi *
      ((∑ n ∈ Finset.range 10, aterm n) + aterm 10 / (1-rho)) := by
  have hr0 : 0 ≤ rho := by norm_num [rho]
  have hr1 : rho < 1 := by norm_num [rho]
  have hm (n : ℕ) : term 2 (n+10) ≤ rho^n * term 2 10 := by
    simpa only [zero_add] using le_geom (u := fun n => term 2 (n+10)) hr0 n
      (fun k _ => aterm_ratio (k+10) (by omega))
  have htail := Summable.tsum_le_tsum hm
    ((summable_nat_add_iff 10).2 (term_summable 2 one_le_two))
    ((summable_geometric_of_lt_one hr0 hr1).mul_right (term 2 10))
  rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1, term_integer] at htail
  have he := Summable.sum_add_tsum_nat_add 10 (term_summable 2 one_le_two)
  rw [← he]
  simp_rw [term_integer]
  rw [← Finset.mul_sum, mul_add]
  simp_rw [term_integer] at htail
  exact add_le_add le_rfl (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htail)

private lemma aterm_upper_numeric :
    (∑ n ∈ Finset.range 10, aterm n) + aterm 10 / (1-rho) ≤ (1672/1000:ℝ) := by
  norm_num [aterm, rho, Finset.sum_range_succ, Nat.factorial, Nat.doubleFactorial]

private lemma hterm_lower (k : ℕ) :
    (∑ n ∈ Finset.range 3, hterm k n) ≤ ∑ n ∈ Finset.range 10, hterm k n := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
  intro n _ _
  unfold hterm
  positivity

private lemma half_lower (k : ℕ) (hk : 1 ≤ k) :
    Real.pi⁻¹^6 * (∑ n ∈ Finset.range 10, hterm k n) ≤ ∑' n, term ((k:ℝ)+1/2) n := by
  have ht : (1:ℝ) ≤ (k:ℝ)+1/2 := by
    have h : (1:ℝ) ≤ k := Nat.one_le_cast.mpr hk
    linarith
  have h := Summable.sum_le_tsum (Finset.range 10)
    (fun n _ => term_nonneg ((k:ℝ)+1/2) ht n)
    (term_summable ((k:ℝ)+1/2) ht)
  simpa only [term_half, Finset.mul_sum] using h

private lemma fval_eq (μ : ℝ) :
    fval (fun _ : Fin 1 => 1) (fun _ : Fin 12 => (1/2:ℝ)) μ 2000 =
      ∑' n, term (μ+1/2) n := by
  unfold fval
  apply tsum_congr
  intro n
  simp [coeff, term, inv_pow, div_eq_mul_inv, add_left_comm, add_assoc, add_comm]
  norm_num

private lemma witness_negative :
    turanian (fun _ : Fin 1 => 1) (fun _ : Fin 12 => (1/2:ℝ))
      1 (1/2) (1/2) 2000 < 0 := by
  have ha : (∑' n, term 2 n) ≤ Real.sqrt Real.pi * (1672/1000:ℝ) :=
    aterm_upper.trans (mul_le_mul_of_nonneg_left aterm_upper_numeric (Real.sqrt_nonneg _))
  have ha0 : 0 ≤ ∑' n, term 2 n := tsum_nonneg (term_nonneg 2 one_le_two)
  have hr : (136700:ℝ) ≤ ∑ n ∈ Finset.range 10, hterm 1 n := by
    refine le_trans ?_ (hterm_lower 1)
    norm_num [hterm, Finset.sum_range_succ, Nat.doubleFactorial, Nat.factorial]
  have hs : (69:ℝ) ≤ ∑ n ∈ Finset.range 10, hterm 2 n := by
    refine le_trans ?_ (hterm_lower 2)
    norm_num [hterm, Finset.sum_range_succ, Nat.doubleFactorial, Nat.factorial]
  have hr' : Real.pi⁻¹^6 * 136700 ≤ ∑' n, term (3/2) n := by
    exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans
      (by convert half_lower 1 NeZero.one_le using 1 <;> norm_num)
  have hs' : Real.pi⁻¹^6 * 69 ≤ ∑' n, term (5/2) n := by
    exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans
      (by convert half_lower 2 NeZero.one_le using 1 <;> norm_num)
  have hpi : (1672/1000:ℝ)^2 * Real.pi^13 < 136700*69 := by
    calc
      _ ≤ (1672/1000:ℝ)^2 * (3.1416:ℝ)^13 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d4.le 13) (sq_nonneg _)
      _ < _ := by norm_num
  have hnum : (Real.sqrt Real.pi * (1672/1000:ℝ))^2 <
      (Real.pi⁻¹^6 * 136700) * (Real.pi⁻¹^6 * 69) := by
    have he : (Real.pi⁻¹^6 * 136700) * (Real.pi⁻¹^6 * 69) =
        (136700*69:ℝ) / Real.pi^12 := by field_simp
    rw [he]
    apply (lt_div_iff₀ (by positivity)).2
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
    nlinarith [hpi]
  have hprod := mul_le_mul hr' hs' (by positivity : 0 ≤ Real.pi⁻¹^6 * 69)
    (tsum_nonneg (term_nonneg (3/2) (by norm_num)))
  have hmid := mul_self_le_mul_self ha0 ha
  unfold turanian
  norm_num only
  simp only [fval_eq (3/2), fval_eq 1, fval_eq 2]
  norm_num only at *
  nlinarith

private lemma witness_cond13 :
    cond13 (fun _ : Fin 1 => (1:ℝ)) (fun _ : Fin 12 => (1/2:ℝ)) := by
  intro j hj
  have hj0 : j = 0 := Nat.lt_one_iff.mp hj
  subst j
  norm_num [esymm_const]

/-- Conjecture 1's universal function nonnegativity assertion is false. -/
theorem result : ¬ claim := by
  intro hclaim
  have h := hclaim 1 12 (fun _ : Fin 1 => 1) (fun _ : Fin 12 => (1/2:ℝ))
    (le_refl 1) (by norm_num) (fun _ => zero_lt_one) (fun _ => one_half_pos)
    witness_cond13
    1 (1/2) (1/2) 2000 (le_refl 1) (by norm_num) (by norm_num)
    (Nat.ofNat_nonneg' 2000)
  exact (not_lt_of_ge h) witness_negative

end D5.S3.Analytic.HypergeometricShiftTuran.FunctionResult
