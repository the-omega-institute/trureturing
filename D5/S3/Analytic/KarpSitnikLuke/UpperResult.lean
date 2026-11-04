/- GID: D5/S3/Analytic/KarpSitnikLuke/UpperResult
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpSitnikLuke/UpperResult
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/KarpSitnikLuke/UpperResult.claim; result=D5/S3/Analytic/KarpSitnikLuke/UpperResult.result; claim=D5/S3/Analytic/KarpSitnikLuke/UpperResult.claim
   digest: Gamma evaluation and an alternating bracket refute the sum-condition upper bound. -/

/-
admission_basis: open-problem-resolution (Karp-Sitnik Conjecture 2; Refuted).
Per-declaration judgment: every row has escape_witness: none.
After expanding same-delivery helpers, the proofs instantiate frozen D5
and Mathlib statements and normalize the resulting rational identities
and inequalities. All theorem rows are bind-only; the settling result
uses the external open-problem-resolution basis.
Frozen dependency keys (declaration identities from the scoped Lean report):
  P: D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.pochRatio
     Lean name: D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult.pochRatio
     statement_id: sha256:f089f44f9bc1b99cb7dea598e4823a0560232e8fd284bb8b9e3b5743a543c931
  T: D5/S3/Analytic/KarpSitnikLuke/Result.hyperTerm
     Lean name: D5.S3.Analytic.KarpSitnikLuke.Result.hyperTerm
     statement_id: sha256:1bb7df8b25cce8e6789d25cb10fd914e120442a7cae2d0487ac08a73cf382ec5
  H: D5/S3/Analytic/KarpSitnikLuke/Result.hyper
     Lean name: D5.S3.Analytic.KarpSitnikLuke.Result.hyper
     statement_id: sha256:6c5b730735feaa738ae231d77a8399918399fcb1731433274f9f2ceeff2bc4a7
  G: D5/S3/Analytic/HypergeometricShiftTuran/Defs.gamma_three
     Lean name: D5.S3.Analytic.HypergeometricShiftTuran.Defs.gamma_three
     statement_id: sha256:b8160fc8dd2e7a06a368c66b586e836b3dce5e67299edfd45091cc7dd8949cd3
Per declaration: name | proof_shape | consumers | frozen dependencies.
  gammaProduct | bind-only (definition) | claim, witness_gamma, result | none
  claim | bind-only (definition) | result | H, T
  u | bind-only (definition) | u_nonneg, u_step, u_half, u_summable, term_eq, witness_summable, witness_lower | P
  u_nonneg | bind-only | u_half, u_summable, witness_lower | P
  u_step | bind-only | u_half | P
  u_half | bind-only | u_summable, witness_lower | P
  u_summable | bind-only | witness_summable, witness_lower | P
  term_eq | bind-only | witness_summable, witness_lower | P, T
  witness_summable | bind-only | result | P, T
  witness_lower | bind-only | result | P, H, T
  witness_gamma | bind-only | result | G
  result | bind-only | settling result | P, H, T, G
The numerical bounds are certified instances with basis refutes.
The only public theorem is result, exactly the negation of claim.
-/

import D5.S3.Analytic.KarpSitnikLuke.Result

/-! # A counterexample to the sum-condition Luke upper bound -/

open scoped BigOperators
open Filter Topology Polynomial
open D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult
open D5.S3.Analytic.KarpSitnikLuke.Result (hyperTerm hyper)
noncomputable section
namespace D5.S3.Analytic.KarpSitnikLuke.UpperResult

def gammaProduct {q : ℕ} (σ : ℝ) (a b : Fin q → ℝ) : ℝ :=
  ∏ i, Real.Gamma (a i) * Real.Gamma (b i - σ) /
    (Real.Gamma (b i) * Real.Gamma (a i - σ))

def claim : Prop :=
  ∀ (q : ℕ) (a b : Fin q → ℝ) (σ x : ℝ),
    (∀ i, 0 < a i) → (∀ i, 0 < b i) → 0 < ∑ i, (b i - a i) →
    0 < σ → (∀ i, σ ≤ a i) → 0 < x → x < 1 →
    Summable (hyperTerm σ a b (-x)) → 0 < gammaProduct σ a b →
    hyper σ a b (-x) < 1 / (1 + x * (gammaProduct σ a b) ^ (1/σ)) ^ σ

private def u (n : ℕ) : ℝ :=
  pochRatio (fun _ : Fin 2 => 2) ![(3/2:ℝ), 3] n * (1/2)^n

private lemma u_nonneg (n : ℕ) : 0 ≤ u n := by
  have hp := (ascPochhammer_pos n (2:ℝ) (by norm_num)).le
  have hq := (ascPochhammer_pos n (3/2:ℝ) (by norm_num)).le
  have hr := (ascPochhammer_pos n (3:ℝ) (by norm_num)).le
  unfold u pochRatio
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  positivity

private lemma u_step (n : ℕ) :
    u (n+1) = ((n+2)^2 / (2 * (n+3/2) * (n+3))) * u n := by
  have hp := (ascPochhammer_pos n (3/2:ℝ) (by norm_num)).ne'
  have hq := (ascPochhammer_pos n (3:ℝ) (by norm_num)).ne'
  have hn : (n:ℝ)+3/2 ≠ 0 := by positivity
  have hn' : (n:ℝ)+3 ≠ 0 := by positivity
  unfold u pochRatio
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, ascPochhammer_succ_eval, pow_succ]
  push_cast
  field_simp
  ring

private lemma u_half (n : ℕ) : u (n+1) ≤ (1/2:ℝ) * u n := by
  rw [u_step]
  apply mul_le_mul_of_nonneg_right _ (u_nonneg n)
  apply (div_le_iff₀ (by positivity : 0 < 2*((n:ℝ)+3/2)*(n+3))).2
  have hn := Nat.cast_nonneg (α := ℝ) n
  nlinarith

private lemma u_summable : Summable u := by
  apply summable_of_ratio_norm_eventually_le (by norm_num : (1/2:ℝ) < 1)
  exact Filter.Eventually.of_forall (fun n => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (u_nonneg _)] using u_half n)

private lemma term_eq (n : ℕ) :
    hyperTerm 1 (fun _ : Fin 2 => 2) ![(3/2:ℝ), 3] (-1/2) n = (-1)^n * u n := by
  have hf : (n.factorial:ℝ) ≠ 0 := by positivity
  unfold hyperTerm u
  rw [ascPochhammer_eval_one, show (-1/2:ℝ) = -1*(1/2) by ring, mul_pow]
  field_simp

private lemma witness_summable :
    Summable (hyperTerm 1 (fun _ : Fin 2 => 2) ![(3/2:ℝ), 3] (-1/2)) := by
  exact (u_summable.alternating).congr (fun n => (term_eq n).symm)

private lemma witness_lower :
    2/3 < hyper 1 (fun _ : Fin 2 => 2) ![(3/2:ℝ), 3] (-1/2) := by
  have hm : Antitone u := antitone_nat_of_succ_le (fun n =>
    (u_half n).trans (mul_le_of_le_one_left (u_nonneg n) (by norm_num)))
  have hu := hm.alternating_series_le_tendsto u_summable.tendsto_alternating_series_tsum 3
  have he : (2/3:ℝ) < (∑ n ∈ Finset.range (2*3), (-1:ℝ)^n * u n) := by
    norm_num [u, pochRatio, Fin.prod_univ_two, Finset.sum_range_succ,
      ascPochhammer_succ_eval, ascPochhammer_zero]
  unfold hyper
  simp_rw [term_eq]
  exact he.trans_le hu

private lemma witness_gamma :
    gammaProduct 1 (fun _ : Fin 2 => 2) ![(3/2:ℝ), 3] = 1 := by
  have hg : Real.Gamma (1/2:ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/2)).ne'
  have hhalf : Real.Gamma (3/2:ℝ) = (1/2) * Real.Gamma (1/2:ℝ) := by
    convert Real.Gamma_add_one (by norm_num : (1/2:ℝ) ≠ 0) using 1 <;> norm_num
  unfold gammaProduct
  rw [Fin.prod_univ_two]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [D5.S3.Analytic.HypergeometricShiftTuran.Defs.gamma_three]
  norm_num [Real.Gamma_two, Real.Gamma_one, hhalf]
  field_simp

theorem result : ¬ claim := by
  intro hc
  have h := hc 2 (fun _ : Fin 2 => 2) ![(3/2:ℝ), 3] 1 (1/2)
    (by norm_num) (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_two]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by simpa only [neg_div] using witness_summable)
    (by rw [witness_gamma]; norm_num)
  rw [witness_gamma] at h
  norm_num only [one_div_one, Real.one_rpow, Real.rpow_one] at h
  exact (not_lt_of_ge witness_lower.le) (by simpa only [neg_div] using h)

end D5.S3.Analytic.KarpSitnikLuke.UpperResult
