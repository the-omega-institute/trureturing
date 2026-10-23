/- GID: D5/S3/Combinatorics/Matroids/SpeyerUniformNormality
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SpeyerUniformNormality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Growing uniform-matroid ranks satisfy the central and local normal limit theorems. -/

/- admission_basis: open-problem-resolution (#15111; Proved)
   Direct frozen dependencies (declaration GID and declaration statement_id):
   F0: D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance sha256:acf3515171050627eccee903208eb3f1d603d5d3ff4cc74a94c0c95259871d6f
   F1: D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance_le_quarter sha256:d26843918e966727ef778f8c78682791d54fdc06c6a8b7c77e5a9601dd05c43e
   F2: D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.stdNormalCDF sha256:bedd42e0116dd2f043fdce1b697eb76e39eb075a733900543f5071ddb4405a7c
   F4: D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.stdNormalPDF sha256:09ec747bd067dc23f72a70f43c419879f8a0a5eaceb77360e81137c6bcbaec5f
   F5: D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.stdNormalPDF_eq_gaussianPDFReal sha256:58d494ec9f13bfb185d13aed064fce12d7eae49cef3f5b9932af21926e310c11
   Module escape_witness: monotone_cdf_pointwise_to_uniform (same-delivery content)
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15743
   Template gap: No divergent-rank-sequence realization or conjunction-of-limits readout is supplied.
   Four-slot evidence missing: source-specific arenas and observation/readout maps,
     exact reconstruction and realization bridges, E1–E8, variation and sensitivity.
   claim states CLT and LLT for the g-polynomial sequence; these predicates use the
   frozen StatLean.HypothesisTesting standard Gaussian owners.
   claim: proof_shape: bind-only; escape_witness: none;
     consumers: statement/type consumers.
   result: proof_shape: content; escape_witness: monotone_cdf_pointwise_to_uniform;
     frozen_dependencies: F0, F1, F2, F4, F5.
     consumers: statement/type consumers.
   g: proof_shape: bind-only; escape_witness: none;
     consumers: g_coeff_succ, g_coeff_zero, g_coeff_above, g_eq_X_mul_q, speyer_variance_bound, speyer_variance_bound_eighth, speyer_variance_eighth_unconditional, speyer_variance_tendsto, g_normalized_bernoulli_multiset, g_bernoulli_factorization, claim, result.
   qAB: proof_shape: bind-only; escape_witness: none;
     consumers: qAB_coeff, qAB_coeff_above, g_eq_X_mul_q, qAB_logderivative_zero, H_reflect_transport, qAB_splits, qAB_pos, qAB_roots_lt, q_splits_roots, speyer_variance_bound, speyer_variance_bound_eighth, speyer_variance_eighth_unconditional, g_normalized_bernoulli_multiset, g_bernoulli_factorization.
   choose_triple_sum: proof_shape: bind-only; escape_witness: none;
     consumers: qAB_coeff.
   qAB_coeff: proof_shape: bind-only; escape_witness: none;
     consumers: g_eq_X_mul_q, qAB_logderivative_zero.
   qAB_coeff_above: proof_shape: bind-only; escape_witness: none;
     consumers: g_eq_X_mul_q.
   choose_cast_factorial: proof_shape: bind-only; escape_witness: none;
     consumers: g_eq_X_mul_q.
   g_coeff_succ: proof_shape: bind-only; escape_witness: none;
     consumers: g_eq_X_mul_q.
   g_coeff_zero: proof_shape: bind-only; escape_witness: none;
     consumers: g_eq_X_mul_q.
   g_coeff_above: proof_shape: bind-only; escape_witness: none;
     consumers: g_eq_X_mul_q.
   g_eq_X_mul_q: proof_shape: bind-only; escape_witness: none;
     consumers: speyer_variance_bound, g_normalized_bernoulli_multiset.
   sigmaSq_X_sub_C: proof_shape: bind-only; escape_witness: none;
     consumers: sigmaSq_root_prod.
   root_prod_eval_ne_zero: proof_shape: bind-only; escape_witness: none;
     consumers: sigmaSq_root_prod, sigmaSq_splits.
   sigmaSq_root_prod: proof_shape: bind-only; escape_witness: none;
     consumers: sigmaSq_splits.
   sigmaSq_splits: proof_shape: bind-only; escape_witness: none;
     consumers: sigmaSq_ge_logderivative.
   root_variance_bound: proof_shape: bind-only; escape_witness: none;
     consumers: sigmaSq_ge_logderivative.
   sigmaSq_ge_logderivative: proof_shape: bind-only; escape_witness: none;
     consumers: speyer_variance_bound.
   qAB_logderivative_zero: proof_shape: bind-only; escape_witness: none;
     consumers: speyer_variance_bound.
   splits_derivative: proof_shape: bind-only; escape_witness: none;
     consumers: iterated_derivative_splits.
   iterated_derivative_splits: proof_shape: bind-only; escape_witness: none;
     consumers: H_splits.
   H: proof_shape: bind-only; escape_witness: none;
     consumers: rodrigues_identity, H_eval_zero, H_splits, H_degree_le, H_reflect_transport, qAB_splits.
   derivative_one_sub_pow: proof_shape: bind-only; escape_witness: none;
     consumers: rodrigues_identity.
   descFactorial_balance: proof_shape: bind-only; escape_witness: none;
     consumers: rodrigues_identity.
   rodrigues_identity: proof_shape: bind-only; escape_witness: none;
     consumers: H_splits.
   H_eval_zero: proof_shape: bind-only; escape_witness: none;
     consumers: H_splits.
   H_splits: proof_shape: bind-only; escape_witness: none;
     consumers: qAB_splits.
   splits_reverse: proof_shape: bind-only; escape_witness: none;
     consumers: splits_reflect.
   splits_reflect: proof_shape: bind-only; escape_witness: none;
     consumers: qAB_splits.
   reflect_linear_pow: proof_shape: bind-only; escape_witness: none;
     consumers: H_reflect_transport.
   H_degree_le: proof_shape: bind-only; escape_witness: none;
     consumers: qAB_splits.
   H_reflect_transport: proof_shape: bind-only; escape_witness: none;
     consumers: qAB_splits.
   qAB_splits: proof_shape: bind-only; escape_witness: none;
     consumers: q_splits_roots.
   qAB_pos: proof_shape: bind-only; escape_witness: none;
     consumers: qAB_roots_lt, speyer_variance_bound, g_normalized_bernoulli_multiset.
   qAB_roots_lt: proof_shape: bind-only; escape_witness: none;
     consumers: q_splits_roots.
   q_splits_roots: proof_shape: bind-only; escape_witness: none;
     consumers: speyer_variance_eighth_unconditional, g_normalized_bernoulli_multiset, g_bernoulli_factorization.
   speyer_variance_bound: proof_shape: bind-only; escape_witness: none;
     consumers: speyer_variance_bound_eighth.
   speyer_variance_bound_eighth: proof_shape: bind-only; escape_witness: none;
     consumers: speyer_variance_eighth_unconditional.
   speyer_variance_eighth_unconditional: proof_shape: bind-only; escape_witness: none;
     consumers: speyer_variance_tendsto.
   speyer_variance_tendsto: proof_shape: bind-only; escape_witness: none;
     consumers: result.
   normalized_mul: proof_shape: bind-only; escape_witness: none;
     consumers: normalized_root_prod, normalized_splits, g_normalized_bernoulli_multiset.
   normalized_C: proof_shape: bind-only; escape_witness: none;
     consumers: normalized_splits.
   normalized_X: proof_shape: bind-only; escape_witness: none;
     consumers: g_normalized_bernoulli_multiset.
   bernoulliP_mem: proof_shape: bind-only; escape_witness: none;
     consumers: g_bernoulli_factorization.
   normalized_linear: proof_shape: bind-only; escape_witness: none;
     consumers: normalized_root_prod.
   normalized_root_prod: proof_shape: bind-only; escape_witness: none;
     consumers: normalized_splits.
   normalized_splits: proof_shape: bind-only; escape_witness: none;
     consumers: g_normalized_bernoulli_multiset.
   g_normalized_bernoulli_multiset: proof_shape: bind-only; escape_witness: none;
     consumers: g_bernoulli_factorization.
   multiset_prod_fin: proof_shape: bind-only; escape_witness: none;
     consumers: g_bernoulli_factorization.
   g_bernoulli_factorization: proof_shape: bind-only; escape_witness: none;
     consumers: result.
-/

import D5.S3.Analytic.Probability.BernoulliTriangularLimits
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

noncomputable section
open Polynomial Finset Filter Real Set MeasureTheory ProbabilityTheory Topology
open scoped BigOperators unitInterval Interval
namespace D5.S3.Combinatorics.Matroids.SpeyerUniformNormality

open D5.S3.Analytic.Probability.UniformCDFConvergence
open D5.S3.Analytic.Probability.BernoulliTriangularLimits
def g (n d : ℕ) : ℝ[X] := ∑ i ∈ Finset.Icc 1 (min d (n - d)),
  C (((n - i - 1).factorial : ℝ) /
    ((d - i).factorial * (n - d - i).factorial * (i - 1).factorial)) * X ^ i


private def qAB (a b : ℕ) : ℝ[X] := ∑ j ∈ range (a+1), C ((a.choose j * b.choose j : ℕ) : ℝ) * (X+1)^j


private lemma choose_triple_sum (a b k : ℕ) (hab : a ≤ b) (hk : k ≤ a) :
    ∑ j ∈ range (a+1), a.choose j * b.choose j * j.choose k =
      a.choose k * (a-k+b).choose (b-k) := by
  have hext : (∑ j ∈ range (a+1), a.choose j * b.choose j * j.choose k) =
      ∑ j ∈ range (b+1), a.choose j * b.choose j * j.choose k := by
    apply sum_subset (range_mono (by omega))
    intro j hj hja
    have h : a < j := by simpa using hja
    simp [Nat.choose_eq_zero_of_lt h]
  rw [hext]
  have hsplit : b+1 = k + (b-k+1) := by omega
  rw [hsplit, sum_range_add]
  have hz : (∑ j ∈ range k, a.choose j * b.choose j * j.choose k) = 0 := by
    apply sum_eq_zero
    intro j hj
    simp [Nat.choose_eq_zero_of_lt (mem_range.mp hj)]
  rw [hz, zero_add]
  calc
    _ = a.choose k * ∑ j ∈ range (b-k+1), (a-k).choose j * b.choose (b-k-j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hkj : k ≤ k+j := by omega
      have hle : k+j ≤ b := by have := mem_range.mp hj; omega
      have heq : b-(k+j) = b-k-j := by omega
      rw [show a.choose (k+j) * b.choose (k+j) * (k+j).choose k =
        (a.choose (k+j) * (k+j).choose k) * b.choose (k+j) by ring,
        Nat.choose_mul hkj, Nat.add_sub_cancel_left,
        ← Nat.choose_symm hle, heq]
      ring
    _ = a.choose k * (a-k+b).choose (b-k) := by
      rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]


private lemma qAB_coeff (a b k : ℕ) (hab : a ≤ b) (hk : k ≤ a) :
    (qAB a b).coeff k = (a.choose k * (a-k+b).choose (b-k) : ℕ) := by
  simp only [qAB, finsetSum_coeff, coeff_C_mul, coeff_X_add_one_pow]
  norm_cast
  exact choose_triple_sum a b k hab hk


private lemma qAB_coeff_above (a b k : ℕ) (hk : a < k) : (qAB a b).coeff k = 0 := by
  simp only [qAB, finsetSum_coeff, coeff_C_mul, coeff_X_add_one_pow]
  apply sum_eq_zero
  intro j hj
  have hjk : j < k := by have := mem_range.mp hj; omega
  simp [Nat.choose_eq_zero_of_lt hjk]


private lemma choose_cast_factorial (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) = (n.factorial : ℝ) / ((k.factorial : ℝ) * ((n-k).factorial : ℝ)) := by
  exact Nat.cast_choose ℝ hk

private lemma g_coeff_succ (n d k : ℕ) (hd : 2 ≤ d) (hn : 2*d ≤ n) (hk : k < d) :
    (g n d).coeff (k+1) =
    ((n-k-2).factorial : ℝ) / ((d-k-1).factorial * (n-d-k-1).factorial * k.factorial) := by
  have hmin : min d (n-d) = d := min_eq_left (by omega)
  simp only [g, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [sum_eq_single (k+1)]
  · simp only [if_pos rfl, mul_one, hmin]
    rw [show n-(k+1)-1 = n-k-2 by omega,
      show d-(k+1) = d-k-1 by omega,
      show n-d-(k+1) = n-d-k-1 by omega,
      show k+1-1=k by omega]
    simp
  · intro b hb hbk
    simp [Ne.symm hbk]
  · intro h
    exfalso
    apply h
    simp only [hmin, Finset.mem_Icc]
    omega


private lemma g_coeff_zero (n d : ℕ) : (g n d).coeff 0 = 0 := by
  simp only [g, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  apply sum_eq_zero
  intro i hi
  have h : i ≠ 0 := by have := (mem_Icc.mp hi).1; omega
  simp [Ne.symm h]


private lemma g_coeff_above (n d k : ℕ) (hn : 2*d ≤ n) (hk : d < k) :
    (g n d).coeff k = 0 := by
  simp only [g, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  apply sum_eq_zero
  intro i hi
  have h : k ≠ i := by have := (mem_Icc.mp hi).2; omega
  simp [h]


private lemma g_eq_X_mul_q (n d : ℕ) (hd : 2 ≤ d) (hn : 2*d ≤ n) :
    g n d = X * qAB (d-1) (n-d-1) := by
  have hab : d-1 ≤ n-d-1 := by omega
  have hq : qAB (d-1) (n-d-1) = qAB (d-1) (n-d-1) := by
    simp only [qAB, show d-1+1=d by omega]
  ext k
  cases k with
  | zero => simp [g_coeff_zero]
  | succ k =>
    rw [coeff_X_mul, hq]
    by_cases hk : k < d
    · rw [g_coeff_succ n d k hd hn hk, qAB_coeff _ _ _ hab (by omega)]
      rw [Nat.cast_mul, choose_cast_factorial _ _ (by omega),
        choose_cast_factorial (d-1-k+(n-d-1)) (n-d-1-k) (by omega)]
      have he1 : d-1-k+(n-d-1) = n-k-2 := by omega
      have he2 : d-1-k+(n-d-1)-(n-d-1-k) = d-1 := by omega
      have he3 : d-1-k = d-k-1 := by omega
      have he4 : n-d-1-k = n-d-k-1 := by omega
      rw [he2, he1, he3, he4]
      have hf1 : ((d-1).factorial : ℝ) ≠ 0 := by exact_mod_cast (d-1).factorial_ne_zero
      have hf2 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      have hf3 : ((d-k-1).factorial : ℝ) ≠ 0 := by exact_mod_cast (d-k-1).factorial_ne_zero
      have hf4 : ((n-d-k-1).factorial : ℝ) ≠ 0 := by exact_mod_cast (n-d-k-1).factorial_ne_zero
      field_simp
    · rw [g_coeff_above n d (k+1) hn (by omega), qAB_coeff_above _ _ _ (by omega)]



private lemma sigmaSq_X_sub_C (r : ℝ) (hr : r < -1) :
    sigmaSq (X-C r) = (-r)/(1-r)^2 := by
  have he : 1-r ≠ 0 := by linarith
  simp only [sigmaSq, mu, derivative_sub, derivative_X, derivative_C,
    sub_zero, derivative_one, eval_zero, eval_one, eval_sub, eval_X, eval_C, zero_div, zero_add]
  field_simp
  <;> ring


private lemma root_prod_eval_ne_zero (s : Multiset ℝ) (hs : ∀ r ∈ s, r < -1) :
    ((s.map (fun r => (X-C r : ℝ[X]))).prod).eval 1 ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have hr : r < -1 := hs r (by simp)
    have ht : ∀ z ∈ s, z < -1 := fun z hz => hs z (by simp [hz])
    simp only [Multiset.map_cons, Multiset.prod_cons, eval_mul]
    apply mul_ne_zero
    · simp only [eval_sub, eval_X, eval_C]
      linarith
    · exact ih ht


private lemma sigmaSq_root_prod (s : Multiset ℝ) (hs : ∀ r ∈ s, r < -1) :
    sigmaSq ((s.map (fun r => (X-C r : ℝ[X]))).prod) =
      (s.map (fun r => (-r)/(1-r)^2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [sigmaSq, mu]
  | cons r s ih =>
    have hr : r < -1 := hs r (by simp)
    have htail : ∀ z ∈ s, z < -1 := fun z hz => hs z (by simp [hz])
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [sigmaSq_mul _ _ (by simp only [eval_sub, eval_X, eval_C]; linarith)
      (root_prod_eval_ne_zero s htail), sigmaSq_X_sub_C r hr, ih htail]


private lemma sigmaSq_splits (f : ℝ[X]) (hf : f.Splits) (hfne : f ≠ 0)
    (hr : ∀ r ∈ f.roots, r < -1) :
    sigmaSq f = (f.roots.map (fun r => (-r)/(1-r)^2)).sum := by
  conv_lhs => rw [hf.eq_prod_roots]
  rw [sigmaSq_mul _ _ (by simpa using leadingCoeff_ne_zero.mpr hfne)
      (root_prod_eval_ne_zero f.roots hr), sigmaSq_C, zero_add,
      sigmaSq_root_prod _ hr]


private lemma root_variance_bound (r : ℝ) (hr : r < -1) :
    (1/4:ℝ) * (1/(-r)) ≤ (-r)/(1-r)^2 := by
  have hrp : 0 < -r := by linarith
  have hep : 0 < 1-r := by linarith
  have heq : (1/4:ℝ) * (1/(-r)) = 1 / (4*(-r)) := by ring
  rw [heq]
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<4*(-r)) (sq_pos_of_pos hep)).mpr
  nlinarith


private lemma sigmaSq_ge_logderivative (f : ℝ[X]) (hf : f.Splits)
    (hf0 : f.eval 0 ≠ 0) (hr : ∀ r ∈ f.roots, r < -1) :
    (f.derivative.eval 0 / f.eval 0)/4 ≤ sigmaSq f := by
  have hfne : f ≠ 0 := by intro h; simp [h] at hf0
  rw [sigmaSq_splits f hf hfne hr, hf.eval_derivative_div_eval_of_ne_zero hf0]
  rw [← Multiset.sum_map_div]
  apply Multiset.sum_map_le_sum_map
  intro r hrmem
  simp only [zero_sub]
  calc
    (1/(-r))/4 = (1/4:ℝ)*(1/(-r)) := by ring
    _ ≤ (-r)/(1-r)^2 := root_variance_bound r (hr r hrmem)


private lemma qAB_logderivative_zero (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (qAB a b).derivative.eval 0 / (qAB a b).eval 0 = (a:ℝ)*b/(a+b) := by
  have hb : 1 ≤ b := by omega
  have h0 : (qAB a b).eval 0 = ((a+b).choose b : ℝ) := by
    rw [← coeff_zero_eq_eval_zero, qAB_coeff a b 0 hab (by omega)]
    simp
  have h1 : (qAB a b).derivative.eval 0 =
      (a:ℝ) * ((a+b-1).choose (b-1) : ℝ) := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative, qAB_coeff a b 1 hab ha]
    simp only [Nat.choose_one_right, Nat.cast_mul, Nat.cast_one, mul_one]
    rw [show a-1+b = a+b-1 by omega]
    simp
  have he : (a+b-1+1) = a+b := by omega
  have heb : b-1+1=b := by omega
  have hmul : ((a+b-1).choose (b-1) : ℝ) * (a+b) = ((a+b).choose b : ℝ) * b := by
    have h := Nat.add_one_mul_choose_eq (a+b-1) (b-1)
    rw [he, heb] at h
    exact_mod_cast (by simpa only [Nat.mul_comm] using h)
  have hden : ((a+b).choose b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : b ≤ a+b)).ne'
  have hsum : (a:ℝ)+b ≠ 0 := by
    have : 0 < (a:ℝ) := by exact_mod_cast (by omega : 0<a)
    positivity
  rw [h0,h1]
  apply (div_eq_div_iff hden hsum).mpr
  nlinarith [hmul]


open Polynomial Finset Filter Real

private lemma splits_derivative {p : ℝ[X]} (hp : p.Splits) : p.derivative.Splits := by
  rw [splits_iff_card_roots]
  have hc := card_roots_le_derivative p
  have hd := p.derivative.card_roots'
  have he := hp.natDegree_eq_card_roots
  rw [natDegree_derivative] at hd ⊢
  omega


private lemma iterated_derivative_splits {p : ℝ[X]} (hp : p.Splits) (k : ℕ) :
    (derivative^[k] p).Splits := by
  induction k with
  | zero => exact hp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact splits_derivative ih
open Polynomial Finset Filter Real
open scoped BigOperators

private def H (a b : ℕ) : ℝ[X] := ∑ j ∈ range (a+1),
  C ((a.choose j * b.choose j : ℕ) : ℝ) * (-X)^j * (1-X)^(a-j)

private lemma derivative_one_sub_pow (b j : ℕ) :
    derivative^[j] ((1-X : ℝ[X])^b) =
      C ((-1:ℝ)^j * (b.descFactorial j:ℝ)) * (1-X)^(b-j) := by
  have h := iterate_derivative_comp_one_sub_X (X^b : ℝ[X]) j
  rw [iterate_derivative_X_pow_eq_C_mul] at h
  simpa [mul_comp, pow_comp, ← C_pow, ← C_mul, mul_assoc] using h

private lemma descFactorial_balance (a b j : ℕ) (hj : j ≤ a) :
    a.descFactorial (a-j) * b.descFactorial j = a.factorial * b.choose j := by
  rw [Nat.descFactorial_eq_factorial_mul_choose b j]
  rw [← mul_assoc, mul_comm (a.descFactorial (a-j)) j.factorial]
  have he : j.factorial * a.descFactorial (a-j) = a.factorial := by
    simpa only [Nat.sub_sub_self hj] using Nat.factorial_mul_descFactorial (Nat.sub_le a j)
  rw [he]

private lemma rodrigues_identity (a b : ℕ) (hab : a ≤ b) :
    derivative^[a] ((X:ℝ[X])^a * (1-X)^b) =
      C (a.factorial:ℝ) * (1-X)^(b-a) * H a b := by
  rw [iterate_derivative_mul, H, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hja : j ≤ a := by have := mem_range.mp hj; omega
  have he : b-j = (b-a)+(a-j) := by omega
  rw [iterate_derivative_X_pow_eq_C_mul, derivative_one_sub_pow,
    Nat.sub_sub_self hja, he, pow_add, neg_pow]
  simp only [nsmul_eq_mul, C_mul, C_pow, C_neg, map_one, Nat.cast_mul, C_eq_natCast]
  have hbal : (a.descFactorial (a-j):ℝ[X]) * b.descFactorial j =
      (a.factorial:ℝ[X]) * b.choose j := by exact_mod_cast descFactorial_balance a b j hja
  linear_combination (a.choose j : ℝ[X]) * (-1:ℝ[X])^j * X^j *
    (1-X)^(b-a) * (1-X)^(a-j) * hbal

private lemma H_eval_zero (a b : ℕ) : (H a b).eval 0 = 1 := by
  simp only [H, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_neg, eval_X,
    eval_sub, eval_one, neg_zero, sub_zero, one_pow, mul_one]
  rw [sum_eq_single 0]
  · simp
  · intro j hj hj0
    simp [zero_pow (by omega : j ≠ 0)]
  · simp


private lemma H_splits (a b : ℕ) (hab : a ≤ b) :
    (H a b).Splits := by
  have hp : ((X:ℝ[X])^a * (1-X)^b).Splits := by
    apply Splits.mul (Splits.X.pow a)
    have hlin : (1-X:ℝ[X]).Splits := by
      simpa only [neg_sub, C_1] using (Splits.X_sub_C (1:ℝ)).neg
    exact hlin.pow b
  have hi := iterated_derivative_splits hp a
  have h0 : derivative^[a] ((X:ℝ[X])^a * (1-X)^b) ≠ 0 := by
    intro he
    have he0 := congrArg (fun p : ℝ[X] => p.eval 0) he
    rw [rodrigues_identity a b hab] at he0
    simp [H_eval_zero, Nat.factorial_ne_zero] at he0
  have hdvd : H a b ∣ derivative^[a] ((X:ℝ[X])^a * (1-X)^b) := by
    rw [rodrigues_identity a b hab]
    exact dvd_mul_left _ _
  exact hi.of_dvd h0 hdvd
open Polynomial Finset Filter Real
open scoped BigOperators

private lemma splits_reverse {p : ℝ[X]} (hp : p.Splits) : p.reverse.Splits := by
  refine Submonoid.closure_induction ?_ (by simpa only [← C_1, reverse_C] using Splits.C (1:ℝ)) ?_ hp
  · rintro f (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · simp
    · apply Splits.of_natDegree_le_one
      exact (reverse_natDegree_le _).trans (by simp)
  · intro f h hf hh ihf ihh
    rw [reverse_mul_of_domain]
    exact ihf.mul ihh

private lemma splits_reflect {p : ℝ[X]} (hp : p.Splits) (n : ℕ) (hn : p.natDegree ≤ n) :
    (p.reflect n).Splits := by
  have he := reflect_mul p (1:ℝ[X]) (F:=p.natDegree) (G:=n-p.natDegree)
    le_rfl (by simp)
  simp only [Nat.add_sub_of_le hn, mul_one, reflect_one] at he
  rw [he]
  exact (splits_reverse hp).mul (Splits.X.pow _)

private lemma reflect_linear_pow (p : ℝ[X]) (hp : p.natDegree ≤ 1) (j : ℕ) :
    (p^j).reflect j = (p.reflect 1)^j := by
  induction j with
  | zero => simp [reflect_one]
  | succ j ih =>
    rw [pow_succ, reflect_mul _ _ (by simpa using natDegree_pow_le_of_le j hp) hp, ih, pow_succ]

private lemma H_degree_le (a b : ℕ) : (H a b).natDegree ≤ a := by
  unfold H
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjle : j ≤ a := by have := mem_range.mp hj; omega
  rw [mul_assoc]
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_mul_le).trans
  have h1 : (1-X : ℝ[X]).natDegree ≤ 1 := by compute_degree
  have h2 : ((1-X:ℝ[X])^(a-j)).natDegree ≤ a-j := by
    simpa only [mul_one] using natDegree_pow_le_of_le (a-j) h1
  have h3 : ((-X:ℝ[X])^j).natDegree ≤ j := by simp
  omega

private lemma H_reflect_transport (a b : ℕ) :
    ((H a b).comp (X+1)).reflect a = C ((-1:ℝ)^a) * qAB a b := by
  let reflection : ℝ[X] →+ ℝ[X] :=
    { toFun := fun f => f.reflect a
      map_zero' := by simp
      map_add' := fun f h => reflect_add f h a }
  rw [H, Polynomial.sum_comp]
  change reflection (∑ j ∈ range (a+1),
    (C ((a.choose j * b.choose j : ℕ) : ℝ) * (-X)^j * (1-X)^(a-j)).comp (X+1)) = _
  rw [map_sum]
  change (∑ j ∈ range (a+1),
    ((C ((a.choose j * b.choose j : ℕ) : ℝ) * (-X)^j * (1-X)^(a-j)).comp (X+1)).reflect a) = _
  rw [qAB, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjle : j ≤ a := by have := mem_range.mp hj; omega
  simp only [mul_comp, C_comp, pow_comp, neg_comp, X_comp, sub_comp, one_comp]
  have hs : (1 - (X+1) : ℝ[X]) = -X := by ring
  rw [hs, mul_assoc, reflect_C_mul]
  have he : a = j+(a-j) := by omega
  have hf := reflect_mul ((-(X+1):ℝ[X])^j) ((-X:ℝ[X])^(a-j))
    (F:=j) (G:=a-j)
    (by simpa only [mul_one] using natDegree_pow_le_of_le j (by compute_degree : (-(X+1):ℝ[X]).natDegree ≤ 1))
    (by simp)
  rw [← he] at hf
  rw [hf, reflect_linear_pow _ (by compute_degree) j,
    reflect_linear_pow _ (by simp) (a-j)]
  have hlin : (-(X+1):ℝ[X]).reflect 1 = -(X+1) := by
    rw [reflect_neg, reflect_add, reflect_one]
    simp [reflect_monomial, revAt]
    ring
  have hx : (-X:ℝ[X]).reflect 1 = -1 := by
    simp [reflect_neg, reflect_monomial, revAt]
  rw [hlin, hx, neg_pow]
  have hc : C ((-1:ℝ)^a) = (-1:ℝ[X])^a := by simp
  rw [hc]
  calc
    _ = C ((a.choose j * b.choose j : ℕ) : ℝ) *
      ((-1:ℝ[X])^j * (-1)^(a-j)) * (X+1)^j := by ring
    _ = _ := by rw [← pow_add, ← he]; ring

private lemma qAB_splits (a b : ℕ) (hab : a ≤ b) : (qAB a b).Splits := by
  have hdeg : ((H a b).comp (X+C 1)).natDegree ≤ a := by
    calc
      _ ≤ (H a b).natDegree * (X+C (1:ℝ)).natDegree := natDegree_comp_le
      _ ≤ a := by
        rw [natDegree_X_add_C, mul_one]
        exact H_degree_le a b
  have hs := splits_reflect ((H_splits a b hab).comp_X_add_C 1) a hdeg
  simp only [C_1] at hs
  rw [H_reflect_transport] at hs
  exact (splits_mul_iff_right (by simp : C ((-1:ℝ)^a) ≠ 0) (Splits.C _)).mp hs

private lemma qAB_pos (a b : ℕ) (x : ℝ) (hx : -1 ≤ x) : 0 < (qAB a b).eval x := by
  simp only [qAB, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
  apply sum_pos'
  · intro j hj
    exact mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
  · exact ⟨0, mem_range.mpr (by omega), by simp⟩

private lemma qAB_roots_lt (a b : ℕ) : ∀ r ∈ (qAB a b).roots, r < -1 := by
  intro r hr
  by_contra hn
  exact (qAB_pos a b r (by linarith)).ne' (isRoot_of_mem_roots hr).eq_zero

private lemma q_splits_roots (n d : ℕ) (hd : 1 ≤ d) (hn : 2*d ≤ n) :
    (qAB (d-1) (n-d-1)).Splits ∧ ∀ r ∈ (qAB (d-1) (n-d-1)).roots, r < -1 := by
  have he : qAB (d-1) (n-d-1) = qAB (d-1) (n-d-1) := by
    simp only [qAB, show d-1+1=d by omega]
  rw [he]
  exact ⟨qAB_splits _ _ (by omega), qAB_roots_lt _ _⟩
private lemma speyer_variance_bound (n d : ℕ) (hd : 2 ≤ d) (hn : 2*d ≤ n)
    (hsplit : (qAB (d-1) (n-d-1)).Splits) (hroots : ∀ r ∈ (qAB (d-1) (n-d-1)).roots, r < -1) :
    ((d-1 : ℕ) : ℝ) * (n-d-1 : ℕ) / (4 * (n-2 : ℕ)) ≤ sigmaSq (g n d) := by
  have hq1 : (qAB (d-1) (n-d-1)).eval 1 ≠ 0 := (qAB_pos (d-1) (n-d-1) 1 (by norm_num)).ne'
  have hq0 : (qAB (d-1) (n-d-1)).eval 0 ≠ 0 := (qAB_pos (d-1) (n-d-1) 0 (by norm_num)).ne'
  have hq : qAB (d-1) (n-d-1) = qAB (d-1) (n-d-1) := by
    simp only [qAB,show d-1+1=d by omega]
  have hlog := qAB_logderivative_zero (d-1) (n-d-1) (by omega) (by omega)
  rw [← hq] at hlog
  have hbound := sigmaSq_ge_logderivative (qAB (d-1) (n-d-1)) hsplit hq0 hroots
  rw [g_eq_X_mul_q n d hd hn, sigmaSq_mul _ _ (by simp) hq1, sigmaSq_X, zero_add]
  rw [hlog] at hbound
  convert hbound using 1
  have he : d-1+(n-d-1) = n-2 := by omega
  rw [← Nat.cast_add, he]
  ring


private lemma speyer_variance_bound_eighth (n d : ℕ) (hd : 2 ≤ d) (hn : 2*d ≤ n)
    (hsplit : (qAB (d-1) (n-d-1)).Splits) (hroots : ∀ r ∈ (qAB (d-1) (n-d-1)).roots, r < -1) :
    ((d-1 : ℕ) : ℝ) / 8 ≤ sigmaSq (g n d) := by
  apply le_trans _ (speyer_variance_bound n d hd hn hsplit hroots)
  have hnp : (0:ℝ) < (n-2 : ℕ) := by exact_mod_cast (by omega : 0<n-2)
  have hb : (n-2 : ℕ) ≤ 2*(n-d-1 : ℕ) := by omega
  have hbR : ((n-2 : ℕ) : ℝ) ≤ 2*((n-d-1 : ℕ) : ℝ) := by exact_mod_cast hb
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 4*(n-2 : ℕ))).mpr
  have ha : (0:ℝ) ≤ (d-1 : ℕ) := by positivity
  nlinarith
private lemma speyer_variance_eighth_unconditional (n d : ℕ) (hd : 2 ≤ d) (hn : 2*d ≤ n) :
    ((d-1 : ℕ) : ℝ) / 8 ≤ sigmaSq (g n d) := by
  obtain ⟨hs,hr⟩ := q_splits_roots n d (by omega) hn
  exact speyer_variance_bound_eighth n d hd hn hs hr


private lemma speyer_variance_tendsto (d : ℕ → ℕ)
    (hvalid : ∀ᶠ n in atTop, 1 ≤ d n ∧ d n ≤ n/2)
    (hd : Tendsto d atTop atTop) :
    Tendsto (fun n => sigmaSq (g n (d n))) atTop atTop := by
  refine tendsto_atTop.2 fun B => ?_
  obtain ⟨M,hM⟩ := exists_nat_gt (8*B+1)
  filter_upwards [hvalid, hd.eventually_ge_atTop (M+2)] with n hv hdn
  have hd2 : 2 ≤ d n := by omega
  have hn : 2*d n ≤ n := by omega
  have hbound := speyer_variance_eighth_unconditional n (d n) hd2 hn
  have hdcast : (M:ℝ)+2 ≤ (d n:ℝ) := by exact_mod_cast hdn
  have he : ((d n-1:ℕ):ℝ) = (d n:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [he] at hbound
  linarith

private lemma normalized_mul (f h : ℝ[X]) : normalized (f*h) = normalized f * normalized h := by
  simp only [normalized, eval_mul, mul_inv_rev, map_mul]
  ring


private lemma normalized_C (c : ℝ) (hc : c ≠ 0) : normalized (C c) = 1 := by
  simp [normalized, ← C_mul, hc]


private lemma normalized_X : normalized (X:ℝ[X]) = X := by simp [normalized]


private lemma bernoulliP_mem (r : ℝ) (hr : r < -1) : (1/(1-r)) ∈ Set.Ioo (0:ℝ) 1 := by
  constructor
  · exact one_div_pos.mpr (by linarith)
  · exact (div_lt_one (by linarith : 0<1-r)).mpr (by linarith)


private lemma normalized_linear (r : ℝ) (hr : r < -1) :
    normalized (X-C r) = bernoulliPGF ((1/(1-r))) := by
  have he : 1-r ≠ 0 := by linarith
  have hcoef : (1-r)⁻¹ * (-r) = 1-(1-r)⁻¹ := by field_simp; ring
  simp only [normalized, eval_sub, eval_X, eval_C, bernoulliPGF,
    one_div, map_sub, map_one]
  have hcoefP := congrArg C hcoef
  simp only [map_mul, map_neg, map_sub, map_one] at hcoefP
  linear_combination hcoefP


private lemma normalized_root_prod (s : Multiset ℝ) (hs : ∀ r ∈ s, r < -1) :
    normalized ((s.map (fun r => (X-C r:ℝ[X]))).prod) =
      (s.map (fun r => bernoulliPGF ((1/(1-r))))).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [normalized]
  | cons r s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [normalized_mul, normalized_linear r (hs r (by simp)), ih (by aesop)]


private lemma normalized_splits (f : ℝ[X]) (hf : f.Splits) (hfne : f ≠ 0)
    (hr : ∀ r ∈ f.roots, r < -1) :
    normalized f = (f.roots.map (fun r => bernoulliPGF ((1/(1-r))))).prod := by
  conv_lhs => rw [hf.eq_prod_roots]
  rw [normalized_mul, normalized_C _ (leadingCoeff_ne_zero.mpr hfne), one_mul,
    normalized_root_prod f.roots hr]


private lemma g_normalized_bernoulli_multiset (n d : ℕ) (hd : 2 ≤ d) (hn : 2*d ≤ n) :
    normalized (g n d) = X *
      ((qAB (d-1) (n-d-1)).roots.map (fun r => bernoulliPGF ((1/(1-r))))).prod := by
  rw [g_eq_X_mul_q n d hd hn, normalized_mul, normalized_X]
  have hs := q_splits_roots n d (by omega) hn
  rw [normalized_splits _ hs.1 (by
    intro h; have := qAB_pos (d-1) (n-d-1) 1 (by norm_num); simp [h] at this) hs.2]
private lemma multiset_prod_fin (s : Multiset ℝ) (f : ℝ → ℝ[X]) :
    (s.map f).prod = ∏ i : Fin s.toList.length, f (s.toList.get i) := by
  rw [← Fin.prod_ofFn]
  change (s.map f).prod = (List.ofFn (f ∘ s.toList.get)).prod
  rw [← List.map_ofFn, List.ofFn_get]
  exact (Multiset.prod_map_toList s f).symm


private lemma g_bernoulli_factorization (n d : ℕ) (hd : 2 ≤ d) (hn : 2*d ≤ n) :
    ∃ m : ℕ, ∃ p : Fin m → unitInterval,
      (∀ i, (p i:ℝ) ∈ Set.Ioo (0:ℝ) 1) ∧
      normalized (g n d) = X * ∏ i, bernoulliPGF (p i:ℝ) := by
  let s := (qAB (d-1) (n-d-1)).roots
  let r (i : Fin s.toList.length) : ℝ := s.toList.get i
  have hr (i : Fin s.toList.length) : r i < -1 := by
    exact (q_splits_roots n d (by omega) hn).2 (r i)
      (by
        change s.toList.get i ∈ s
        exact Multiset.mem_toList.mp (List.get_mem s.toList i))
  let p (i : Fin s.toList.length) : unitInterval :=
    ⟨(1/(1-r i)), (bernoulliP_mem (r i) (hr i)).1.le,
      (bernoulliP_mem (r i) (hr i)).2.le⟩
  refine ⟨s.toList.length, p, fun i => bernoulliP_mem (r i) (hr i), ?_⟩
  rw [g_normalized_bernoulli_multiset n d hd hn, multiset_prod_fin]



def claim : Prop := ∀ d : ℕ → ℕ,
  (∀ᶠ n in atTop, 1 ≤ d n ∧ d n ≤ n / 2) → Tendsto d atTop atTop →
  CLT (fun n => g n (d n)) ∧ LLT (fun n => g n (d n))


open Polynomial Finset Filter Real
open scoped BigOperators unitInterval Topology

theorem result : claim := by
  intro d hadm hd
  have hpair : ∀ᶠ n in atTop, 2≤d n ∧ 2*d n≤n := by
    filter_upwards [hadm,hd.eventually_ge_atTop 2] with n hn hdn
    exact ⟨hdn,by omega⟩
  have hex : ∀ n, ∃ m : ℕ, ∃ p : Fin m → unitInterval,
      (2≤d n ∧ 2*d n≤n) → normalized (g n (d n)) = X*∏ i, bernoulliPGF (p i:ℝ) := by
    intro n
    by_cases hn : 2≤d n ∧ 2*d n≤n
    · obtain ⟨m,p,hp,hpgf⟩ := g_bernoulli_factorization n (d n) hn.1 hn.2
      exact ⟨m,p,fun _ => hpgf⟩
    · exact ⟨0,(fun i => Fin.elim0 i),fun h => False.elim (hn h)⟩
  choose m p hp using hex
  have hfac : ∀ᶠ n in atTop, normalized (g n (d n)) = X*∏ i, bernoulliPGF (p n i:ℝ) :=
    hpair.mono (fun n hn => hp n hn)
  have hV : Tendsto (fun n => rowVariance (p n)) atTop atTop := by
    apply (speyer_variance_tendsto d hadm hd).congr'
    filter_upwards [hfac] with n hpgf
    exact (factorization_moments (p n) hpgf).2.2
  exact bernoulli_polynomial_uniform_limits (fun n => g n (d n)) p hfac hV

end D5.S3.Combinatorics.Matroids.SpeyerUniformNormality
