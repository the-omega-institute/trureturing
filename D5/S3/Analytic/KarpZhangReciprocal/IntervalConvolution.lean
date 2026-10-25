/- GID: D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangReciprocal/IntervalConvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.Bernoulli]
   utility: none
   digest: Symmetric interval convolutions increase when positive parameters are balanced. -/

import Mathlib.NumberTheory.Bernoulli
import D5.S3.Analytic.KarpZhangReciprocal.BirthDeath
import D5.S3.Analytic.KummerRatio.Series

/-!
admission_basis: escape-witness
content theorem: symmetric_tail, through score_variance_bound.
escape_witness: Reversible rates on an arbitrary finite interval absorb the score variance
into expected coefficient curvature, including both endpoints. The resulting
logarithmic concavity on lines s+t=S and symmetry imply the tail comparison.
Only this direction of concavity is asserted. Coefficient calculus, including
the curvature estimate obtained from Mathlib Faulhaber (sum_range_pow), is
bind-only and supplies inputs to the reversible-rate variance argument.

Per-declaration proof_shape (Coeff names belong to the coefficient namespace;
other local names belong to IntervalConvolution; cross-module names have
prefix D5.S3.Analytic):
* Coeff.c: proof_shape: bind-only (definition); escape_witness: none;
  consumers: Coeff.c_deriv, Coeff.c_pos, Coeff.c_succ, Coeff.coefficient_calculus, F, balance, coefficient_step, rate_curvature, score_deriv, score_variance_bound, symmetric, weight, weight_deriv, weight_pos, KarpZhangReciprocal.Result.abel_reduction, KarpZhangReciprocal.Result.delta.
* Coeff.lambda: proof_shape: bind-only (definition); escape_witness: none;
  consumers: Coeff.c_deriv, Coeff.c_succ, Coeff.coefficient_calculus, Coeff.lambda_antitone, Coeff.lambda_deriv, Coeff.lambda_pos, balance, birth, coefficient_step, death, rate_curvature, score_deriv, score_variance_bound, weight_deriv, weight_pos.
* Coeff.eta: proof_shape: bind-only (definition); escape_witness: none;
  consumers: Coeff.c_deriv, Coeff.coefficient_calculus, Coeff.curvature_bound, Coeff.eta_deriv, Coeff.lambda_deriv, Coeff.psi, Coeff.psi_deriv, coefficient_step, rate_curvature, score_deriv, score_variance_bound, weight_deriv, weight_pos.
* Coeff.psi: proof_shape: bind-only (definition); escape_witness: none;
  consumers: Coeff.c_deriv, Coeff.coefficient_calculus, Coeff.psi_deriv, coefficient_step, rate_curvature, score, score_deriv, score_variance_bound, weight_deriv, weight_pos.
* Coeff.chi: proof_shape: bind-only (definition); escape_witness: none;
  consumers: Coeff.chi_nonneg, Coeff.coefficient_calculus, Coeff.curvature_bound, Coeff.psi_deriv, coefficient_step, curvature, rate_curvature, score_deriv, score_variance_bound, weight_deriv, weight_pos.
* Coeff.c_pos: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus.
* Coeff.lambda_pos: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus.
* Coeff.c_succ: proof_shape: bind-only; escape_witness: none;
  reuse: KummerRatio.Series.coeff_succ at s := 2*t and c := t;
  consumers: Coeff.c_deriv, coefficient_calculus.
* Coeff.lambda_antitone: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus.
* Coeff.lambda_deriv: proof_shape: bind-only; escape_witness: none;
  consumers: c_deriv.
* Coeff.eta_deriv: proof_shape: bind-only; escape_witness: none;
  consumers: psi_deriv.
* Coeff.c_deriv: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus.
* Coeff.psi_deriv: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus.
* Coeff.chi_nonneg: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus.
* Coeff.curvature_summand: proof_shape: bind-only; escape_witness: none;
  consumers: curvature_bound.
* Coeff.square_sum_lower: proof_shape: bind-only; escape_witness: none;
  consumers: curvature_bound.
* Coeff.curvature_bound: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_calculus.
* Coeff.coefficient_calculus: proof_shape: bind-only; escape_witness: none;
  consumers: coefficient_step, rate_curvature, score_deriv, score_variance_bound, weight_deriv, weight_pos.

* F: proof_shape: bind-only (definition); escape_witness: none;
  consumers: shift_tail, symmetric, symmetric_tail, KarpZhangReciprocal.Result.abel_reduction, KarpZhangReciprocal.Result.reciprocal_half.
* weight: proof_shape: bind-only (definition); escape_witness: none;
  consumers: balance, score_variance_bound, slice_concave, symmetric_tail, total_pos, weight_deriv, weight_pos.
* score: proof_shape: bind-only (definition); escape_witness: none;
  consumers: score_deriv, score_variance_bound, slice_concave, weight_deriv.
* curvature: proof_shape: bind-only (definition); escape_witness: none;
  consumers: score_deriv, score_variance_bound, slice_concave.
* birth: proof_shape: bind-only (definition); escape_witness: none;
  consumers: balance, rate_curvature, score_variance_bound.
* death: proof_shape: bind-only (definition); escape_witness: none;
  consumers: balance, rate_curvature, score_variance_bound.
* weight_pos: proof_shape: bind-only; escape_witness: none;
  consumers: score_variance_bound, total_pos.
* total_pos: proof_shape: bind-only; escape_witness: none;
  consumers: score_variance_bound, slice_concave, symmetric_tail.
* coefficient_step: proof_shape: bind-only; escape_witness: none;
  consumers: balance.
* balance: proof_shape: bind-only; escape_witness: none;
  consumers: score_variance_bound.
* rate_curvature: proof_shape: bind-only; escape_witness: none;
  consumers: score_variance_bound.
* square_split: proof_shape: bind-only; escape_witness: none;
  reuse: Finset.sq_sum_div_le_sum_sq_div on Fin 2;
  consumers: score_variance_bound.
* score_variance_bound: proof_shape: content; escape_witness: score_variance_bound;
  consumers: slice_concave.
* variance_expand: proof_shape: bind-only; escape_witness: none;
  consumers: slice_concave.
* weight_deriv: proof_shape: bind-only; escape_witness: none;
  consumers: slice_concave.
* score_deriv: proof_shape: bind-only; escape_witness: none;
  consumers: slice_concave.
* slice_concave: proof_shape: content; escape_witness: score_variance_bound;
  consumers: symmetric_tail.
* symmetric: proof_shape: bind-only; escape_witness: none;
  consumers: shift_tail, symmetric_tail.
* symmetric_tail: proof_shape: content; escape_witness: score_variance_bound;
  consumers: shift_tail.
* shift_tail: proof_shape: content; escape_witness: score_variance_bound;
  consumers: KarpZhangReciprocal.Result.reciprocal_half.

Direct frozen D5 dependencies, with same-delivery helpers recursively inlined:
* F1: GID D5/S3/Analytic/KummerRatio/Defs.kummerCoeff;
  declaration statement_id:
  sha256:2ada6e56e131a4bdb7cccbc60aec3a351bc0b05a8b9544c75077cb676503abe7.
* F2: GID D5/S3/Analytic/KummerRatio/Series.coeff_succ;
  declaration statement_id:
  sha256:65529d42eed8f7a2af577c9bed21aaa15e926d5c89a7a18bc06b6b51c9936da9.
Per-declaration live-path dependencies (F labels above; omitted declarations: none):
* KarpZhangReciprocal.Coeff.c_succ: F1, F2.
* KarpZhangReciprocal.Coeff.c_deriv: F1, F2.
* KarpZhangReciprocal.Coeff.coefficient_calculus: F1, F2.
* KarpZhangReciprocal.IntervalConvolution.weight_pos: F1, F2.
* KarpZhangReciprocal.IntervalConvolution.total_pos: F1, F2.
* KarpZhangReciprocal.IntervalConvolution.coefficient_step: F1, F2.
* KarpZhangReciprocal.IntervalConvolution.balance: F1, F2.
* KarpZhangReciprocal.IntervalConvolution.rate_curvature: F1, F2.
* KarpZhangReciprocal.IntervalConvolution.score_variance_bound: F1, F2.
* KarpZhangReciprocal.IntervalConvolution.weight_deriv: F1, F2.
* KarpZhangReciprocal.IntervalConvolution.score_deriv: F1, F2.
* KarpZhangReciprocal.IntervalConvolution.slice_concave: F1, F2.
* KarpZhangReciprocal.IntervalConvolution.symmetric_tail: F1, F2.
* KarpZhangReciprocal.IntervalConvolution.shift_tail: F1, F2.
All KarpZhang dependencies are same-delivery declarations.
Consumers are taken from compiled proof
terms, with declaration types also counted for definitions. The listed
content witnesses remain on the corresponding live mathematical paths.
Utility is none: all statements are general identities or inequalities,
not bounded enumeration, checkers, numerical reductions or certified instances.
-/

noncomputable section
open scoped BigOperators Topology
open Finset

open Polynomial

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
  have h := D5.S3.Analytic.KummerRatio.Series.coeff_succ (2 * t) ht n
  simpa only [D5.S3.Analytic.KummerRatio.Defs.kummerCoeff, c, lambda,
    div_mul_eq_mul_div, mul_comm] using h

private theorem lambda_antitone {t : ℝ} (ht : 0 < t) :
    Antitone (fun j : ℕ => lambda j t) := by
  intro i j hij
  have hi : 0 < t + i := by positivity
  have hj : 0 < t + j := by positivity
  have hij' : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
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
  have hj' : (j : ℝ) ≤ N := Nat.cast_le.mpr hj
  have hD : (2 * t + j) ^ 2 * (t + j) ^ 2 ≤
      (2 * t + N) ^ 2 * (t + N) ^ 2 := by
    gcongr
  exact div_le_div₀ (by positivity)
    (by nlinarith [mul_nonneg ht.le (Nat.cast_nonneg (α := ℝ) j)])
    (by positivity) hD

private theorem square_sum_lower (N : ℕ) :
    ((N : ℝ) + 1) * (N : ℝ) ^ 2 ≤ ∑ j ∈ range (N + 1), 3 * (j : ℝ) ^ 2 := by
  have h := sum_range_pow (N + 1) 2
  norm_num [Finset.sum_range_succ] at h
  rw [← Finset.sum_range_succ] at h
  have hreal := congrArg (fun x : ℚ => (x : ℝ)) h
  push_cast at hreal
  rw [← mul_sum]
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
    HasDerivAt (psi n) (-chi n t) t ∧
    0 ≤ chi n t ∧
    (n : ℝ) * eta (n - 1) t ^ 2 ≤ chi n t ∧
    Antitone (fun j : ℕ => lambda j t) := by
  refine ⟨c_pos n ht, lambda_pos n ht, ?_, c_deriv n ht,
    psi_deriv n ht, chi_nonneg n ht, curvature_bound n ht, lambda_antitone ht⟩
  rw [c_succ n ht]
  field_simp [ne_of_gt (c_pos n ht), ne_of_gt (show 0 < (n : ℝ) + 1 by positivity)]
  <;> ring

end D5.S3.Analytic.KarpZhangReciprocal.Coeff


namespace D5.S3.Analytic.KarpZhangReciprocal.IntervalConvolution

open Coeff

/-- For `L ≤ U ≤ m`, the convolution over all indices from `L` through `U`. -/
def F (m L U : ℕ) (s t : ℝ) : ℝ :=
  ∑ i ∈ range (U - L + 1), c (L + i) s * c (m - (L + i)) t

private def weight (m L i : ℕ) (s t : ℝ) : ℝ :=
  c (L + i) s * c (m - (L + i)) t

private def score (m L i : ℕ) (s t : ℝ) : ℝ :=
  psi (L + i) s - psi (m - (L + i)) t

private def curvature (m L i : ℕ) (s t : ℝ) : ℝ :=
  chi (L + i) s + chi (m - (L + i)) t

private def birth (m L n : ℕ) (s : ℝ) (i : ℕ) : ℝ :=
  if i < n then (m - (L + i) : ℕ) * lambda (L + i) s else 0

private def death (m L : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else (L + i : ℕ) * lambda (m - (L + i)) t

private theorem weight_pos (m L i : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 < weight m L i s t :=
  mul_pos (coefficient_calculus (L + i) hs).1
    (coefficient_calculus (m - (L + i)) ht).1

private theorem total_pos (m L n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 < ∑ i ∈ range (n + 1), weight m L i s t := by
  apply sum_pos
  · intro i _
    exact weight_pos m L i hs ht
  · exact ⟨0, mem_range.mpr (Nat.succ_pos n)⟩

private theorem coefficient_step (k : ℕ) {s : ℝ} (hs : 0 < s) :
    c (k + 1) s * (k + 1 : ℕ) = c k s * lambda k s := by
  have h : c (k + 1) s / c k s = lambda k s / ((k + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (coefficient_calculus k hs).2.2.1
  have hc := ne_of_gt (coefficient_calculus k hs).1
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  have h' := (div_eq_div_iff hc hk).mp h
  simpa only [mul_comm] using h'

private theorem balance (m L n : ℕ) (hm : L + n ≤ m)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (i : ℕ) (hi : i < n) :
    weight m L i s t * birth m L n s i =
      weight m L (i + 1) s t * death m L t (i + 1) := by
  have hi0 : i + 1 ≠ 0 := Nat.succ_ne_zero i
  have he : m - (L + i) = (m - (L + (i + 1))) + 1 := by omega
  have hleft := coefficient_step (L + i) hs
  have hright := coefficient_step (m - (L + (i + 1))) ht
  have hidx : L + (i + 1) = (L + i) + 1 := (Nat.add_assoc L i 1).symm
  simp only [birth, if_pos hi, death, if_neg hi0, weight]
  rw [← he] at hright
  rw [hidx]
  calc
    _ = (c (L + i) s * lambda (L + i) s) *
        (c (m - (L + i)) t * (m - (L + i) : ℕ)) := by ring
    _ = (c (L + i + 1) s * (L + i + 1 : ℕ)) *
        (c (m - (L + (i + 1))) t * lambda (m - (L + (i + 1))) t) := by
      rw [← hleft, hright]
    _ = _ := by rw [hidx]; ring

private theorem rate_curvature (m L n : ℕ) (hm : L + n ≤ m)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (i : ℕ) (hi : i < n) :
    lambda (L + i) s + lambda (m - (L + (i + 1))) t ≤
      BirthDeath.kappa (birth m L n s) (death m L t) i := by
  have hi' : L + i < m := by omega
  have he : m - (L + i) = m - (L + (i + 1)) + 1 := by omega
  have hA := (coefficient_calculus (L + i) hs).2.1
  have hB := (coefficient_calculus (m - (L + (i + 1))) ht).2.1
  have hp : lambda (L + i) s ≤ birth m L n s i - birth m L n s (i + 1) := by
    simp only [birth, if_pos hi]
    split_ifs with hnext
    · have hmono := (coefficient_calculus 0 hs).2.2.2.2.2.2.2
      have hcmp := hmono (show L + i ≤ L + (i + 1) by omega)
      have hmul := mul_nonneg (Nat.cast_nonneg (α := ℝ)
        (m - (L + (i + 1)))) (sub_nonneg.mpr hcmp)
      have he' : ((m - (L + i) : ℕ) : ℝ) =
          (m - (L + (i + 1)) : ℕ) + 1 := by exact_mod_cast he
      nlinarith
    · have hdeg : (1 : ℝ) ≤ (m - (L + i) : ℕ) := by exact_mod_cast (show 1 ≤ m - (L + i) by omega)
      have hmul := mul_nonneg (sub_nonneg.mpr hdeg) hA.le
      nlinarith
  have hr : lambda (m - (L + (i + 1))) t ≤
      death m L t (i + 1) - death m L t i := by
    have hnext : i + 1 ≠ 0 := Nat.succ_ne_zero i
    simp only [death, if_neg hnext]
    split_ifs with hzero
    · subst i
      have hdeg : (1 : ℝ) ≤ (L + (0 + 1) : ℕ) := by exact_mod_cast (show 1 ≤ L + (0 + 1) by omega)
      have hmul := mul_nonneg (sub_nonneg.mpr hdeg) hB.le
      nlinarith
    · have hmono := (coefficient_calculus 0 ht).2.2.2.2.2.2.2
      have hcmp := hmono (show m - (L + (i + 1)) ≤ m - (L + i) by omega)
      have hmul := mul_nonneg (Nat.cast_nonneg (α := ℝ) (L + i))
        (sub_nonneg.mpr hcmp)
      have he' : ((L + (i + 1) : ℕ) : ℝ) = (L + i : ℕ) + 1 := Nat.cast_add_one (L + i)
      nlinarith
  unfold BirthDeath.kappa
  linarith

private theorem square_split {A B K X Y : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hK : A + B ≤ K) : (X + Y) ^ 2 / K ≤ X ^ 2 / B + Y ^ 2 / A := by
  calc
    (X + Y) ^ 2 / K ≤ (X + Y) ^ 2 / (A + B) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (add_pos hA hB) hK
    _ ≤ X ^ 2 / B + Y ^ 2 / A := by
      simpa [Fin.sum_univ_two, add_comm] using
        (Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin 2))
          (fun i => if i = 0 then X else Y)
          (g := fun i => if i = 0 then B else A)
          (by intro i _; split_ifs <;> assumption))

/-- The variance absorption step for an arbitrary interval, including a singleton. -/
private theorem score_variance_bound (m L n : ℕ) (hm : L + n ≤ m)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    let Z := ∑ i ∈ range (n + 1), weight m L i s t
    let π := fun i => weight m L i s t / Z
    BirthDeath.variance n π (fun i => score m L i s t) ≤
      ∑ i ∈ range (n + 1), π i * curvature m L i s t := by
  dsimp only
  let Z := ∑ i ∈ range (n + 1), weight m L i s t
  let π := fun i => weight m L i s t / Z
  let p := birth m L n s
  let r := death m L t
  let H := fun i => score m L i s t
  have hZ : 0 < Z := total_pos m L n hs ht
  have hπ (i : ℕ) (_ : i ≤ n) : 0 < π i := div_pos (weight_pos m L i hs ht) hZ
  have hprob : ∑ i ∈ range (n + 1), π i = 1 := by
    dsimp only [π]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hZ)
  have hp : p n = 0 := by simp [p, birth]
  have hr : r 0 = 0 := rfl
  have hpp (i : ℕ) (hi : i < n) : 0 < p i := by
    dsimp only [p]
    rw [birth, if_pos hi]
    exact mul_pos (by exact_mod_cast (show 0 < m - (L + i) by omega))
      (coefficient_calculus (L + i) hs).2.1
  have hrr (i : ℕ) (hi : 0 < i) (_ : i ≤ n) : 0 < r i := by
    dsimp only [r]
    rw [death, if_neg (by omega : i ≠ 0)]
    exact mul_pos (by exact_mod_cast (show 0 < L + i by omega))
      (coefficient_calculus (m - (L + i)) ht).2.1
  have hb (i : ℕ) (hi : i < n) : π i * p i = π (i + 1) * r (i + 1) := by
    dsimp only [π, p, r]
    have h := balance m L n hm hs ht i hi
    exact (by simpa only [div_mul_eq_mul_div] using congrArg (fun x : ℝ => x / Z) h)
  have hk (i : ℕ) (hi : i < n) : 0 < BirthDeath.kappa p r i :=
    lt_of_lt_of_le (add_pos (coefficient_calculus (L + i) hs).2.1
      (coefficient_calculus (m - (L + (i + 1))) ht).2.1)
      (rate_curvature m L n hm hs ht i hi)
  have hv := BirthDeath.variance_bound n π p r H hπ hprob hp hr hpp hrr hb hk
  have hedge (i : ℕ) (hi : i < n) :
      π i * p i / BirthDeath.kappa p r i * (H (i + 1) - H i) ^ 2 ≤
        π (i + 1) * chi (L + (i + 1)) s + π i * chi (m - (L + i)) t := by
    let k := L + i
    let ell := m - (L + i)
    let A := lambda k s
    let B := lambda (ell - 1) t
    let X := eta k s
    let Y := eta (ell - 1) t
    have he : ell = m - (L + (i + 1)) + 1 := by dsimp [ell]; omega
    have he' : ell - 1 = m - (L + (i + 1)) := Nat.sub_sub m (L + i) 1
    have hk' : L + (i + 1) = k + 1 := (Nat.add_assoc L i 1).symm
    have hA : 0 < A := (coefficient_calculus k hs).2.1
    have hB : 0 < B := (coefficient_calculus (ell - 1) ht).2.1
    have hK : A + B ≤ BirthDeath.kappa p r i := by
      simpa only [A, B, k, he'] using rate_curvature m L n hm hs ht i hi
    have hdiff : H (i + 1) - H i = X + Y := by
      dsimp only [H, score, X, Y]
      have hpsi : psi ell t = psi (ell - 1) t + eta (ell - 1) t := by
        conv_lhs => rw [show ell = (ell - 1) + 1 by omega]
        exact sum_range_succ _ _
      rw [← he', hk']
      change psi (k + 1) s - psi (ell - 1) t - (psi k s - psi ell t) = _
      rw [hpsi, show psi (k + 1) s = psi k s + eta k s by
        exact sum_range_succ _ _]
      ring
    have hC : (k + 1 : ℕ) * X ^ 2 ≤ chi (k + 1) s := by
      simpa only [X, Nat.add_sub_cancel] using
        (coefficient_calculus (k + 1) hs).2.2.2.2.2.2.1
    have hD : (ell : ℝ) * Y ^ 2 ≤ chi ell t :=
      (coefficient_calculus ell ht).2.2.2.2.2.2.1
    have hpval : p i = (ell : ℝ) * A := by simp only [p, birth, if_pos hi, ell, A, k]
    have hrval : r (i + 1) = (k + 1 : ℕ) * B := rfl
    have hC' : X ^ 2 / B ≤ chi (k + 1) s / r (i + 1) := by
      rw [hrval]
      apply (div_le_div_iff₀ hB (mul_pos (by positivity) hB)).2
      nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hC)]
    have hD' : Y ^ 2 / A ≤ chi ell t / p i := by
      rw [hpval]
      apply (div_le_div_iff₀ hA (mul_pos (by exact_mod_cast (show 0 < ell by omega)) hA)).2
      nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hD)]
    have hbase := (square_split hA hB hK).trans (add_le_add hC' hD')
    have hmul := mul_le_mul_of_nonneg_left hbase
      (mul_nonneg (hπ i (by omega)).le (hpp i hi).le)
    have hb' : π i * p i / r (i + 1) = π (i + 1) := by
      rw [hb i hi]
      exact mul_div_cancel_right₀ _ (ne_of_gt (hrr (i + 1) (by omega) (by omega)))
    rw [hdiff, hk']
    calc
      _ = π i * p i * ((X + Y) ^ 2 / BirthDeath.kappa p r i) := by ring
      _ ≤ π i * p i * (chi (k + 1) s / r (i + 1) + chi ell t / p i) := hmul
      _ = π (i + 1) * chi (k + 1) s + π i * chi ell t := by
        rw [mul_add]
        have hfirst : π i * p i * (chi (k + 1) s / r (i + 1)) =
            (π i * p i / r (i + 1)) * chi (k + 1) s :=
              (mul_comm_div (π i * p i) (r (i + 1)) (chi (k + 1) s)).symm
        rw [hfirst, hb']
        field_simp [ne_of_gt (hpp i hi)]
        <;> ring
  have hsum := sum_le_sum (fun i hi => hedge i (mem_range.mp hi))
  have hends : (∑ i ∈ range n,
        (π (i + 1) * chi (L + (i + 1)) s + π i * chi (m - (L + i)) t)) ≤
      ∑ i ∈ range (n + 1), π i * curvature m L i s t := by
    simp only [curvature, mul_add, sum_add_distrib]
    rw [sum_range_succ' (fun i => π i * chi (L + i) s),
      sum_range_succ (fun i => π i * chi (m - (L + i)) t)]
    have h0 := mul_nonneg (hπ 0 (by omega)).le
      (coefficient_calculus (L + 0) hs).2.2.2.2.2.1
    have hn := mul_nonneg (hπ n le_rfl).le
      (coefficient_calculus (m - (L + n)) ht).2.2.2.2.2.1
    linarith
  exact hv.trans (hsum.trans hends)

private theorem variance_expand (n : ℕ) (π H : ℕ → ℝ)
    (hprob : ∑ i ∈ range (n + 1), π i = 1) :
    BirthDeath.variance n π H = (∑ i ∈ range (n + 1), π i * H i ^ 2) -
      (∑ i ∈ range (n + 1), π i * H i) ^ 2 := by
  let a := ∑ i ∈ range (n + 1), π i * H i
  change (∑ i ∈ range (n + 1), π i * (H i - a) ^ 2) = _
  calc
    _ = ∑ i ∈ range (n + 1),
        (π i * H i ^ 2 - 2 * a * (π i * H i) + a ^ 2 * π i) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hprob]
      change _ - 2 * a * a + a ^ 2 * 1 = _ - a ^ 2
      ring

private theorem weight_deriv (m L i : ℕ) (S : ℝ) {s : ℝ}
    (hs : 0 < s) (ht : 0 < S - s) :
    HasDerivAt (fun u => weight m L i u (S - u))
      (weight m L i s (S - s) * score m L i s (S - s)) s := by
  have hd := (coefficient_calculus (L + i) hs).2.2.2.1
  have he := ((coefficient_calculus (m - (L + i)) ht).2.2.2.1).comp s
    ((hasDerivAt_id s).const_sub S)
  apply (hd.mul he).congr_deriv
  dsimp [weight, score]
  ring

private theorem score_deriv (m L i : ℕ) (S : ℝ) {s : ℝ}
    (hs : 0 < s) (ht : 0 < S - s) :
    HasDerivAt (fun u => score m L i u (S - u))
      (-curvature m L i s (S - s)) s := by
  have hd := (coefficient_calculus (L + i) hs).2.2.2.2.1
  have he := ((coefficient_calculus (m - (L + i)) ht).2.2.2.2.1).comp s
    ((hasDerivAt_id s).const_sub S)
  apply (hd.sub he).congr_deriv
  dsimp [curvature]
  ring

private theorem slice_concave (m L n : ℕ) (hm : L + n ≤ m) (S : ℝ) :
    ConcaveOn ℝ (Set.Ioo 0 S)
      (fun s => Real.log (∑ i ∈ range (n + 1), weight m L i s (S - s))) := by
  let Z := fun s => ∑ i ∈ range (n + 1), weight m L i s (S - s)
  let N := fun s => ∑ i ∈ range (n + 1),
    weight m L i s (S - s) * score m L i s (S - s)
  let Q := fun s => ∑ i ∈ range (n + 1),
    weight m L i s (S - s) *
      (score m L i s (S - s) ^ 2 - curvature m L i s (S - s))
  have hZ (s : ℝ) (hs : s ∈ Set.Ioo 0 S) : 0 < Z s :=
    total_pos m L n hs.1 (sub_pos.mpr hs.2)
  have dZ (s : ℝ) (hs : s ∈ Set.Ioo 0 S) : HasDerivAt Z (N s) s :=
    HasDerivAt.fun_sum (fun i _ => weight_deriv m L i S hs.1 (sub_pos.mpr hs.2))
  have dN (s : ℝ) (hs : s ∈ Set.Ioo 0 S) : HasDerivAt N (Q s) s := by
    apply HasDerivAt.fun_sum
    intro i _
    apply ((weight_deriv m L i S hs.1 (sub_pos.mpr hs.2)).mul
      (score_deriv m L i S hs.1 (sub_pos.mpr hs.2))).congr_deriv
    ring
  have dlog (s : ℝ) (hs : s ∈ Set.Ioo 0 S) :
      HasDerivAt (fun u => Real.log (Z u)) (N s / Z s) s :=
    (dZ s hs).log (ne_of_gt (hZ s hs))
  have dquot (s : ℝ) (hs : s ∈ Set.Ioo 0 S) :
      HasDerivAt (fun u => N u / Z u) ((Q s * Z s - N s ^ 2) / Z s ^ 2) s := by
    convert (dN s hs).div (dZ s hs) (ne_of_gt (hZ s hs)) using 1 <;> ring
  have hnonpos (s : ℝ) (hs : s ∈ Set.Ioo 0 S) :
      (Q s * Z s - N s ^ 2) / Z s ^ 2 ≤ 0 := by
    let π := fun i => weight m L i s (S - s) / Z s
    let H := fun i => score m L i s (S - s)
    let C := fun i => curvature m L i s (S - s)
    have hp : ∑ i ∈ range (n + 1), π i = 1 := by
      dsimp only [π]
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt (hZ s hs))
    have hv := score_variance_bound m L n hm hs.1 (sub_pos.mpr hs.2)
    change BirthDeath.variance n π H ≤ ∑ i ∈ range (n + 1), π i * C i at hv
    rw [variance_expand n π H hp] at hv
    have hmean : (∑ i ∈ range (n + 1), π i * H i) = N s / Z s := by
      dsimp only [π, H, N]
      simp only [div_mul_eq_mul_div]
      rw [← Finset.sum_div]
    have hQ : Q s / Z s = (∑ i ∈ range (n + 1), π i * H i ^ 2) -
        ∑ i ∈ range (n + 1), π i * C i := by
      dsimp only [Q, π, H, C]
      rw [Finset.sum_div, ← sum_sub_distrib]
      apply sum_congr rfl
      intro i _
      ring
    rw [hmean] at hv
    have he : (Q s * Z s - N s ^ 2) / Z s ^ 2 = Q s / Z s - (N s / Z s) ^ 2 := by
      field_simp [ne_of_gt (hZ s hs)]
      <;> ring
    rw [he, hQ]
    linarith
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioo 0 S)
    (f' := fun s => N s / Z s)
    (f'' := fun s => (Q s * Z s - N s ^ 2) / Z s ^ 2)
  · intro s hs
    exact (dlog s hs).continuousAt.continuousWithinAt
  · intro s hs
    exact (dlog s (interior_subset hs)).hasDerivWithinAt
  · intro s hs
    exact (dquot s (interior_subset hs)).hasDerivWithinAt
  · intro s hs
    exact hnonpos s (interior_subset hs)

private theorem symmetric (m q : ℕ) (hq : 2 * q ≤ m) (s t : ℝ) :
    F m q (m - q) s t = F m q (m - q) t s := by
  unfold F
  let n := m - q - q
  change (∑ i ∈ range (n + 1), _) = ∑ i ∈ range (n + 1), _
  rw [← sum_range_reflect (fun i => c (q + i) s * c (m - (q + i)) t) (n + 1)]
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  simp only [Nat.add_sub_cancel]
  rw [show q + (n - i) = m - (q + i) by dsimp [n] at *; omega,
    show m - (m - (q + i)) = q + i by dsimp [n] at *; omega, mul_comm]

/-- A symmetric interval convolution increases under a balancing of its positive parameters.
The endpoint case `a = d` and all singleton index intervals are included. -/
theorem symmetric_tail (m q : ℕ) (hq : 2 * q ≤ m)
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (hsum : a + d = b + c) :
    F m q (m - q) a d ≤ F m q (m - q) b c := by
  let S := a + d
  have hd : 0 < d := lt_of_lt_of_le ha (hab.trans (hbc.trans hcd))
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hc : 0 < c := lt_of_lt_of_le hb hbc
  have hqa : q + (m - q - q) ≤ m := by omega
  have hconc := slice_concave m q (m - q - q) hqa S
  change ConcaveOn ℝ (Set.Ioo 0 S) (fun s => Real.log (F m q (m - q) s (S - s))) at hconc
  have hpa : a ∈ Set.Ioo 0 S := ⟨ha, by dsimp [S]; linarith⟩
  have hpd : d ∈ Set.Ioo 0 S := ⟨hd, by dsimp [S]; linarith⟩
  have hmin := hconc.min_le_of_mem_Icc hpa hpd ⟨hab, hbc.trans hcd⟩
  have hsa : S - a = d := add_sub_cancel_left a d
  have hsd : S - d = a := add_sub_cancel_right a d
  have hsb : S - b = c := (eq_sub_of_add_eq' hsum.symm).symm
  rw [hsa, hsd, hsb, ← symmetric m q hq a d, min_self] at hmin
  exact (Real.log_le_log_iff (total_pos m q (m - q - q) ha hd)
    (total_pos m q (m - q - q) hb hc)).mp hmin

/-- The tail inequality with arbitrary nonnegative shifts; their order is immaterial. -/
theorem shift_tail (m q : ℕ) (hq : 2 * q ≤ m) {μ α β : ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    F m q (m - q) μ (μ + α + β) ≤ F m q (m - q) (μ + α) (μ + β) := by
  by_cases h : α ≤ β
  · exact symmetric_tail m q hq hμ (by linarith) (by linarith) (by linarith)
      (by ring)
  · have he := symmetric_tail m q hq hμ
      (b := μ + β) (c := μ + α) (d := μ + α + β)
      (by linarith) (by linarith) (by linarith) (by ring)
    rw [symmetric m q hq (μ + β) (μ + α)] at he
    exact he

end D5.S3.Analytic.KarpZhangReciprocal.IntervalConvolution
