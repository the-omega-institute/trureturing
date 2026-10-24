/- GID: D5/S3/Analytic/KarpZhangReciprocal/Coeff
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangReciprocal/Coeff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Pochhammer, mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Deriv]
   utility: none
   digest: Reciprocal Pochhammer scores satisfy a uniform degree-curvature bound. -/

import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
admission_basis: escape-witness
content theorem: coefficient_calculus, through curvature_bound.
escape_witness: The uniform score-curvature estimate compares each rational summand with a
common terminal denominator. square_sum_lower supplies the degree-uniform
sum-of-squares inequality by induction; curvature_bound sums the estimates.
Positivity, rational differentiation and the Pochhammer recurrence are
consumed normalization helpers.

Per-declaration proof_shape (local names belong to this namespace;
cross-module names have prefix D5.S3.Analytic):
* c: proof_shape: definition; escape_witness: none;
  consumers: c_deriv, c_pos, c_succ, coefficient_calculus, log_c_deriv, KarpZhangReciprocal.IntervalConvolution.F, KarpZhangReciprocal.IntervalConvolution.balance, KarpZhangReciprocal.IntervalConvolution.coefficient_step, KarpZhangReciprocal.IntervalConvolution.rate_curvature, KarpZhangReciprocal.IntervalConvolution.score_deriv, KarpZhangReciprocal.IntervalConvolution.score_variance_bound, KarpZhangReciprocal.IntervalConvolution.symmetric, KarpZhangReciprocal.IntervalConvolution.weight, KarpZhangReciprocal.IntervalConvolution.weight_deriv, KarpZhangReciprocal.IntervalConvolution.weight_pos, KarpZhangReciprocal.Result.abel_reduction, KarpZhangReciprocal.Result.delta.
* lambda: proof_shape: definition; escape_witness: none;
  consumers: c_deriv, c_succ, coefficient_calculus, lambda_antitone, lambda_deriv, lambda_pos, KarpZhangReciprocal.IntervalConvolution.balance, KarpZhangReciprocal.IntervalConvolution.birth, KarpZhangReciprocal.IntervalConvolution.coefficient_step, KarpZhangReciprocal.IntervalConvolution.death, KarpZhangReciprocal.IntervalConvolution.rate_curvature, KarpZhangReciprocal.IntervalConvolution.score_deriv, KarpZhangReciprocal.IntervalConvolution.score_variance_bound, KarpZhangReciprocal.IntervalConvolution.weight_deriv, KarpZhangReciprocal.IntervalConvolution.weight_pos.
* eta: proof_shape: definition; escape_witness: none;
  consumers: c_deriv, coefficient_calculus, curvature_bound, eta_deriv, lambda_deriv, psi, psi_deriv, KarpZhangReciprocal.IntervalConvolution.coefficient_step, KarpZhangReciprocal.IntervalConvolution.rate_curvature, KarpZhangReciprocal.IntervalConvolution.score_deriv, KarpZhangReciprocal.IntervalConvolution.score_variance_bound, KarpZhangReciprocal.IntervalConvolution.weight_deriv, KarpZhangReciprocal.IntervalConvolution.weight_pos.
* psi: proof_shape: definition; escape_witness: none;
  consumers: c_deriv, coefficient_calculus, log_c_deriv, psi_deriv, KarpZhangReciprocal.IntervalConvolution.coefficient_step, KarpZhangReciprocal.IntervalConvolution.rate_curvature, KarpZhangReciprocal.IntervalConvolution.score, KarpZhangReciprocal.IntervalConvolution.score_deriv, KarpZhangReciprocal.IntervalConvolution.score_variance_bound, KarpZhangReciprocal.IntervalConvolution.weight_deriv, KarpZhangReciprocal.IntervalConvolution.weight_pos.
* chi: proof_shape: definition; escape_witness: none;
  consumers: chi_nonneg, coefficient_calculus, curvature_bound, psi_deriv, KarpZhangReciprocal.IntervalConvolution.coefficient_step, KarpZhangReciprocal.IntervalConvolution.curvature, KarpZhangReciprocal.IntervalConvolution.rate_curvature, KarpZhangReciprocal.IntervalConvolution.score_deriv, KarpZhangReciprocal.IntervalConvolution.score_variance_bound, KarpZhangReciprocal.IntervalConvolution.weight_deriv, KarpZhangReciprocal.IntervalConvolution.weight_pos.
* c_pos: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus, log_c_deriv.
* lambda_pos: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus.
* c_succ: proof_shape: bind-only; escape_witness: none;
  consumers: c_deriv, coefficient_calculus.
* lambda_antitone: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus.
* lambda_deriv: proof_shape: bind-only; escape_witness: none;
  consumers: c_deriv.
* eta_deriv: proof_shape: bind-only; escape_witness: none;
  consumers: psi_deriv.
* c_deriv: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus, log_c_deriv.
* log_c_deriv: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus.
* psi_deriv: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus.
* chi_nonneg: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus.
* curvature_summand: proof_shape: bind-only; escape_witness: none;
  consumers: curvature_bound.
* square_sum_lower: proof_shape: content; escape_witness: square_sum_lower;
  consumers: curvature_bound.
* curvature_bound: proof_shape: content; escape_witness: square_sum_lower;
  consumers: coefficient_calculus.
* coefficient_calculus: proof_shape: content; escape_witness: curvature_bound;
  consumers: KarpZhangReciprocal.IntervalConvolution.coefficient_step, KarpZhangReciprocal.IntervalConvolution.rate_curvature, KarpZhangReciprocal.IntervalConvolution.score_deriv, KarpZhangReciprocal.IntervalConvolution.score_variance_bound, KarpZhangReciprocal.IntervalConvolution.weight_deriv, KarpZhangReciprocal.IntervalConvolution.weight_pos.

Direct frozen D5 dependencies: none; all KarpZhang dependencies are
same-delivery declarations. Consumers are taken from compiled proof
terms, with declaration types also counted for definitions. The listed
content witnesses remain on the corresponding live mathematical paths.
Utility is none: all statements are general identities or inequalities,
not bounded enumeration, checkers, numerical reductions or certified instances.
-/

noncomputable section
open scoped BigOperators Topology
open Finset Polynomial

namespace D5.S3.Analytic.KarpZhangReciprocal.Coeff

/-- The coefficient of the reciprocal-Pochhammer series. -/
def c (n : ℕ) (t : ℝ) : ℝ :=
  (ascPochhammer ℝ n).eval (2 * t) /
    ((ascPochhammer ℝ n).eval t * (n.factorial : ℝ))

/-- The unnormalised adjacent-degree ratio. -/
def lambda (j : ℕ) (t : ℝ) : ℝ := (2 * t + j) / (t + j)

/-- The adjacent-degree score increment, including its zero value at degree zero. -/
def eta (j : ℕ) (t : ℝ) : ℝ := (j : ℝ) / ((2 * t + j) * (t + j))

/-- The logarithmic score, written as a finite sum including the zero summand. -/
def psi (n : ℕ) (t : ℝ) : ℝ := ∑ j ∈ range n, eta j t

/-- Negative logarithmic curvature, written as an explicit finite sum. -/
def chi (n : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ range n, (j : ℝ) * (4 * t + 3 * j) /
    ((2 * t + j) ^ 2 * (t + j) ^ 2)

private theorem c_pos (n : ℕ) {t : ℝ} (ht : 0 < t) : 0 < c n t := by
  exact div_pos (ascPochhammer_pos n _ (by linarith))
    (mul_pos (ascPochhammer_pos n t ht) (by exact_mod_cast n.factorial_pos))

private theorem lambda_pos (j : ℕ) {t : ℝ} (ht : 0 < t) : 0 < lambda j t := by
  unfold lambda
  positivity

private theorem c_succ (n : ℕ) {t : ℝ} (ht : 0 < t) :
    c (n + 1) t = c n t * lambda n t / (n + 1 : ℝ) := by
  have hp := ne_of_gt (ascPochhammer_pos n t ht)
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn : t + n ≠ 0 := by positivity
  have hs : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [c, lambda, ascPochhammer_succ_eval, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hp, hf, hn, hs]
  <;> ring

private theorem lambda_antitone {t : ℝ} (ht : 0 < t) :
    Antitone (fun j : ℕ => lambda j t) := by
  intro i j hij
  have hi : 0 < t + i := by positivity
  have hj : 0 < t + j := by positivity
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hmul := mul_nonneg ht.le (sub_nonneg.mpr hij')
  change (2 * t + (j : ℝ)) / (t + j) ≤ (2 * t + (i : ℝ)) / (t + i)
  rw [div_le_div_iff₀ hj hi]
  nlinarith

private theorem lambda_deriv (j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (lambda j) (lambda j t * eta j t) t := by
  have hd := (((hasDerivAt_id t).const_mul 2).add_const (j : ℝ)).div
    ((hasDerivAt_id t).add_const (j : ℝ)) (by positivity : t + j ≠ 0)
  apply hd.congr_deriv
  dsimp [lambda, eta]
  field_simp [ne_of_gt (show 0 < t + j by positivity),
    ne_of_gt (show 0 < 2 * t + j by positivity)]
  <;> ring

private theorem eta_deriv (j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (eta j)
      (-((j : ℝ) * (4 * t + 3 * j) / ((2 * t + j) ^ 2 * (t + j) ^ 2))) t := by
  have hd := (hasDerivAt_const t (j : ℝ)).div
    ((((hasDerivAt_id t).const_mul 2).add_const (j : ℝ)).mul
      ((hasDerivAt_id t).add_const (j : ℝ)))
    (by positivity : (2 * t + j) * (t + j) ≠ 0)
  apply hd.congr_deriv
  dsimp
  field_simp [ne_of_gt (show 0 < t + j by positivity),
    ne_of_gt (show 0 < 2 * t + j by positivity)]
  <;> ring

private theorem c_deriv (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (c n) (c n t * psi n t) t := by
  induction n with
  | zero =>
    have hc : c 0 = (fun _ : ℝ => 1) := by
      funext u
      simp only [c, ascPochhammer_zero, eval_one, Nat.factorial_zero,
        Nat.cast_one, mul_one, div_one]
    rw [hc]
    simpa only [psi, sum_range_zero, mul_zero] using (hasDerivAt_const t (1 : ℝ))
  | succ n ih =>
    have hd := (ih.mul (lambda_deriv n ht)).div_const (n + 1 : ℝ)
    have he : c (n + 1) =ᶠ[nhds t]
        (fun u => c n u * lambda n u / (n + 1 : ℝ)) := by
      exact (eventually_gt_nhds ht).mono (fun u hu => c_succ n hu)
    have hd' := hd.congr_of_eventuallyEq he
    convert hd' using 1
    rw [c_succ n ht]
    simp only [psi, sum_range_succ]
    ring

private theorem log_c_deriv (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => Real.log (c n u)) (psi n t) t := by
  apply ((c_deriv n ht).log (ne_of_gt (c_pos n ht))).congr_deriv
  exact mul_div_cancel_left₀ (psi n t) (ne_of_gt (c_pos n ht))

private theorem psi_deriv (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (psi n) (-chi n t) t := by
  change HasDerivAt (fun u : ℝ => ∑ j ∈ range n, eta j u) (-chi n t) t
  have hd := HasDerivAt.fun_sum (u := range n) (fun j _ => eta_deriv j ht)
  apply hd.congr_deriv
  change (∑ j ∈ range n,
    -((j : ℝ) * (4 * t + 3 * j) / ((2 * t + j) ^ 2 * (t + j) ^ 2))) =
      -(∑ j ∈ range n,
        (j : ℝ) * (4 * t + 3 * j) / ((2 * t + j) ^ 2 * (t + j) ^ 2))
  rw [sum_neg_distrib]

private theorem chi_nonneg (n : ℕ) {t : ℝ} (ht : 0 < t) : 0 ≤ chi n t := by
  unfold chi
  exact sum_nonneg (fun j _ => by positivity)

/-- A denominator comparison retains enough of every summand for a degree-uniform bound. -/
private theorem curvature_summand {j N : ℕ} {t : ℝ} (ht : 0 < t) (hj : j ≤ N) :
    3 * (j : ℝ) ^ 2 / ((2 * t + N) ^ 2 * (t + N) ^ 2) ≤
      (j : ℝ) * (4 * t + 3 * j) / ((2 * t + j) ^ 2 * (t + j) ^ 2) := by
  have hj' : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hD : (2 * t + j) ^ 2 * (t + j) ^ 2 ≤
      (2 * t + N) ^ 2 * (t + N) ^ 2 := by
    gcongr
  exact div_le_div₀ (by positivity)
    (by nlinarith [mul_nonneg ht.le (Nat.cast_nonneg (α := ℝ) j)])
    (by positivity) hD

private theorem square_sum_lower (N : ℕ) :
    ((N : ℝ) + 1) * (N : ℝ) ^ 2 ≤ ∑ j ∈ range (N + 1), 3 * (j : ℝ) ^ 2 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ]
    simp only [Nat.cast_succ, Nat.cast_add, Nat.cast_one]
    nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- The scalar estimate used to absorb score variance into coefficient curvature. -/
private theorem curvature_bound (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (n : ℝ) * eta (n - 1) t ^ 2 ≤ chi n t := by
  cases n with
  | zero => simp [eta, chi]
  | succ N =>
    have hD : 0 < (2 * t + N) ^ 2 * (t + N) ^ 2 := by positivity
    calc
      ((N + 1 : ℕ) : ℝ) * eta (N + 1 - 1) t ^ 2 =
          (((N : ℝ) + 1) * (N : ℝ) ^ 2) /
            ((2 * t + N) ^ 2 * (t + N) ^ 2) := by
        simp only [Nat.add_sub_cancel, eta, Nat.cast_add, Nat.cast_one]
        field_simp [ne_of_gt (show 0 < t + N by positivity),
          ne_of_gt (show 0 < 2 * t + N by positivity)]
        <;> ring
      _ ≤ (∑ j ∈ range (N + 1), 3 * (j : ℝ) ^ 2) /
          ((2 * t + N) ^ 2 * (t + N) ^ 2) :=
        (div_le_div_iff_of_pos_right hD).2 (square_sum_lower N)
      _ = ∑ j ∈ range (N + 1),
          3 * (j : ℝ) ^ 2 / ((2 * t + N) ^ 2 * (t + N) ^ 2) := by
        simp only [div_eq_mul_inv, sum_mul]
      _ ≤ chi (N + 1) t := by
        apply sum_le_sum
        intro j hj
        exact curvature_summand ht (Nat.le_of_lt_succ (mem_range.mp hj))

/-- Coefficient calculus and the uniform score-curvature estimate, for every positive parameter.
The `n = 0` curvature clause uses the zero score increment, so no exceptional index is needed. -/
theorem coefficient_calculus (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < c n t ∧
    0 < lambda n t ∧
    c (n + 1) t / c n t = lambda n t / (n + 1 : ℝ) ∧
    HasDerivAt (c n) (c n t * psi n t) t ∧
    HasDerivAt (fun u => Real.log (c n u)) (psi n t) t ∧
    HasDerivAt (psi n) (-chi n t) t ∧
    0 ≤ chi n t ∧
    (n : ℝ) * eta (n - 1) t ^ 2 ≤ chi n t ∧
    Antitone (fun j : ℕ => lambda j t) := by
  refine ⟨c_pos n ht, lambda_pos n ht, ?_, c_deriv n ht, log_c_deriv n ht,
    psi_deriv n ht, chi_nonneg n ht, curvature_bound n ht, lambda_antitone ht⟩
  rw [c_succ n ht]
  field_simp [ne_of_gt (c_pos n ht), ne_of_gt (show 0 < (n : ℝ) + 1 by positivity)]
  <;> ring

end D5.S3.Analytic.KarpZhangReciprocal.Coeff
