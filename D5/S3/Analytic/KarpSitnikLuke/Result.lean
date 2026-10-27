/- GID: D5/S3/Analytic/KarpSitnikLuke/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpSitnikLuke/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/KarpSitnikLuke/Result.claim; result=D5/S3/Analytic/KarpSitnikLuke/Result.result; claim=D5/S3/Analytic/KarpSitnikLuke/Result.claim
   digest: A three-term alternating-series bracket refutes the sum-condition Luke bound. -/

/-
admission_basis: open-problem-resolution (Karp-Sitnik Conjecture 1; Refuted).
Per-declaration judgment: all rows have escape_witness: none.
Inlining the same-delivery helpers leaves only frozen pochRatio, Mathlib's
rising-factorial recurrences, geometric comparison, alternating-series bounds
and rational normalization. All theorem rows are bind-only.
Frozen dependency P (declaration identity from the scoped Lean report):
  D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.pochRatio
  Lean name: D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult.pochRatio
  statement_id: sha256:f089f44f9bc1b99cb7dea598e4823a0560232e8fd284bb8b9e3b5743a543c931
Per declaration: name | proof_shape | consumers | frozen dependencies.
  hyperTerm | bind-only (definition) | hyper, claim, term_eq, witness_summable, witness_upper, result | P
  hyper | bind-only (definition) | claim, witness_upper, result | P
  claim | bind-only (definition) | result | P
  u | bind-only (definition) | u_nonneg, u_step, u_half, u_summable, term_eq, witness_summable, witness_upper | none
  u_nonneg | bind-only | u_half, u_summable, witness_upper | none
  u_step | bind-only | u_half | none
  u_half | bind-only | u_summable, witness_upper | none
  u_summable | bind-only | witness_summable, witness_upper | none
  term_eq | bind-only | witness_summable, witness_upper | P
  witness_summable | bind-only | result | P
  witness_upper | bind-only | result | P
  result | bind-only | settling result | P
The utility is certified-instance with basis refutes. The only public theorem
is result, whose conclusion is the exact negation of claim.
-/

import D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult
open scoped BigOperators
open Filter Topology Polynomial
open D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult
noncomputable section
namespace D5.S3.Analytic.KarpSitnikLuke.Result

def hyperTerm {q : ℕ} (σ : ℝ) (a b : Fin q → ℝ) (z : ℝ) (n : ℕ) : ℝ :=
  (ascPochhammer ℝ n).eval σ * pochRatio a b n / (n.factorial : ℝ) * z ^ n

def hyper {q : ℕ} (σ : ℝ) (a b : Fin q → ℝ) (z : ℝ) : ℝ :=
  ∑' n, hyperTerm σ a b z n

def claim : Prop :=
  ∀ (q : ℕ) (a b : Fin q → ℝ) (σ x : ℝ),
    (∀ i, 0 < a i) → (∀ i, 0 < b i) → 0 < ∑ i, (b i - a i) →
    0 < σ → -1 < x → x < 1 → 0 < 1 + x * ∏ i, a i / b i →
    Summable (hyperTerm σ a b (-x)) →
    1 / (1 + x * ∏ i, a i / b i) ^ σ < hyper σ a b (-x)

private def u (n : ℕ) : ℝ :=
  (n.factorial : ℝ) / ((ascPochhammer ℝ n).eval (1/10) * (n+1)) * (1/10)^n

private lemma u_nonneg (n : ℕ) : 0 ≤ u n := by
  have hp := (ascPochhammer_pos n (1/10:ℝ) (by norm_num)).le
  unfold u
  positivity

private lemma u_step (n : ℕ) :
    u (n+1) = ((n+1)^2 / (10 * (n+1/10) * (n+2))) * u n := by
  have hp := (ascPochhammer_pos n (1/10:ℝ) (by norm_num)).ne'
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have hn' : (n:ℝ)+2 ≠ 0 := by positivity
  have hn'' : (n:ℝ)+1/10 ≠ 0 := by positivity
  unfold u
  rw [Nat.factorial_succ, ascPochhammer_succ_eval, pow_succ]
  push_cast
  field_simp
  ring

private lemma u_half (n : ℕ) : u (n+1) ≤ (1/2:ℝ) * u n := by
  rw [u_step]
  apply mul_le_mul_of_nonneg_right _ (u_nonneg n)
  apply (div_le_iff₀ (by positivity : 0 < 10*((n:ℝ)+1/10)*(n+2))).2
  have hn := Nat.cast_nonneg (α := ℝ) n
  nlinarith

private lemma u_summable : Summable u := by
  apply summable_of_ratio_norm_eventually_le (by norm_num : (1/2:ℝ) < 1)
  exact Filter.Eventually.of_forall (fun n => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (u_nonneg _)] using u_half n)

private lemma term_eq (n : ℕ) :
    hyperTerm 1 (fun _ : Fin 2 => 1) ![(1/10:ℝ), 2] (-1/10) n = (-1)^n * u n := by
  have htwo : (ascPochhammer ℝ n).eval 2 = ((n+1).factorial : ℝ) := by
    simpa only [Nat.factorial_one, Nat.cast_one, one_mul, Nat.cast_add, Nat.add_comm, show (1:ℝ)+1=2 by norm_num] using
      factorial_mul_ascPochhammer ℝ 1 n
  have hf : (n.factorial:ℝ) ≠ 0 := by positivity
  unfold hyperTerm pochRatio u
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, ascPochhammer_eval_one, htwo]
  rw [Nat.factorial_succ]
  push_cast
  rw [show (-1/10:ℝ) = -1*(1/10) by ring, mul_pow]
  field_simp

private lemma witness_summable :
    Summable (hyperTerm 1 (fun _ : Fin 2 => 1) ![(1/10:ℝ), 2] (-1/10)) := by
  exact (u_summable.alternating).congr (fun n => (term_eq n).symm)

private lemma witness_upper :
    hyper 1 (fun _ : Fin 2 => 1) ![(1/10:ℝ), 2] (-1/10) < 2/3 := by
  have hm : Antitone u := antitone_nat_of_succ_le (fun n =>
    (u_half n).trans (mul_le_of_le_one_left (u_nonneg n) (by norm_num)))
  have hu := hm.tendsto_le_alternating_series u_summable.tendsto_alternating_series_tsum 1
  have he : (∑ n ∈ Finset.range (2*1+1), (-1:ℝ)^n * u n) < 2/3 := by
    norm_num [u, Finset.sum_range_succ, ascPochhammer_succ_eval, ascPochhammer_zero]
  unfold hyper
  simp_rw [term_eq]
  exact hu.trans_lt he

theorem result : ¬ claim := by
  intro hc
  have h := hc 2 (fun _ : Fin 2 => 1) ![(1/10:ℝ), 2] 1 (1/10)
    (by norm_num) (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_two]) (by norm_num) (by norm_num) (by norm_num)
    (by simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; norm_num) (by simpa only [neg_div] using witness_summable)
  norm_num only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Real.rpow_one] at h
  exact (not_lt_of_ge witness_upper.le) (by simpa only [neg_div] using h)
end D5.S3.Analytic.KarpSitnikLuke.Result
