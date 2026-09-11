/- GID: D5/S3/Arith/GoldenResource/ChainResponseSelectorGap
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/ChainResponseSelectorGap
   mirror-E: none(waiver:general-matrix-family)
   anchors: []
   utility: none
   digest: Non-scalar chain Schur responses have arbitrarily small selector loss. -/

import D5.S3.Arith.GoldenResource.ChainSchurResponse
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
The integer, uniformly bounded two-chain pencils have non-scalar real effective matrices,
but their selector loss tends to zero with an explicit geometric upper bound. This refutes
the transfer of a uniform positive integer selector gap through Schur elimination.
It does not refute `IntegerFischerSelector.integer_log_unique_maximum`, whose domain is
integer matrices, and does not change that theorem.

`p = 1/2` 是**为得到有限 Lean 陈述而选的 selector-price 特化,不是由观察者假设推出的**
(它确落在 `k=2` 的严格窗口 `log(3/2) < 1/2 < log 2` 内)。

The preregistered escape witness is `chain_response_loss_le_geometric`: the integer
recurrence endpoint bound is combined with the scalar logarithmic remainder estimate.
-/

namespace D5.S3.Arith.GoldenResource.ChainResponseSelectorGap

open Matrix ChainSchurResponse TridiagonalChainInverse
open scoped BigOperators

noncomputable section

/-- Selector loss at the chosen price one half, relative to the scalar matrix `2 I`. -/
def chainResponseLoss (n : ℕ) : ℝ := -Real.log (1 - eta n / 2) - eta n / 2

private theorem eta_pos (n : ℕ) : 0 < eta n := by
  have ht : 0 < t n := by
    rw [endpoint_formula]
    exact one_div_pos.mpr (by exact_mod_cast chainDet_pos (n + 1))
  exact div_pos (sq_pos_of_pos ht) (z_pos n)

private theorem eta_le_endpoint_sq (n : ℕ) : eta n ≤ t n ^ 2 := by
  have hz : 1 ≤ z n := by
    have hs : 0 ≤ ∑ i, w n i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    dsimp [z]
    linarith
  exact div_le_self (sq_nonneg _) hz

private theorem eta_le_ninth_pow (n : ℕ) : eta n ≤ 1 / (9 : ℝ) ^ (n + 1) :=
  (eta_le_endpoint_sq n).trans (chain_endpoint_sq_le n)

private theorem eta_le_ninth (n : ℕ) : eta n ≤ 1 / 9 := by
  apply (eta_le_ninth_pow n).trans
  apply one_div_le_one_div_of_le (by norm_num)
  have h : 1 ≤ (9 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  linarith

/-- Every finite effective matrix differs from every scalar diagonal matrix. -/
theorem effective_ne_scalar (n : ℕ) (c : ℝ) :
    effective n 2 1 ≠ diagonal ![c, c] := by
  intro h
  rw [effective_eq] at h
  have h₀ := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) h
  have h₁ := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 1 1) h
  simp only [diagonal_apply_eq, cons_val_zero, cons_val_one, one_mul] at h₀ h₁
  have hp := eta_pos n
  linarith

private theorem log_remainder_bounds {y : ℝ} (_hy : 0 ≤ y) (hy' : y ≤ 1 / 2) :
    0 ≤ -Real.log (1 - y) - y ∧ -Real.log (1 - y) - y ≤ 2 * y ^ 2 := by
  have hd : 0 < 1 - y := by linarith
  constructor
  · have h := Real.log_le_sub_one_of_pos hd
    linarith
  · have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
    rw [Real.log_inv] at h
    have he : (1 - y)⁻¹ - 1 - y = y ^ 2 / (1 - y) := by
      field_simp
      ring
    calc
      -Real.log (1 - y) - y ≤ (1 - y)⁻¹ - 1 - y := sub_le_sub_right h y
      _ = y ^ 2 / (1 - y) := he
      _ ≤ 2 * y ^ 2 := (div_le_iff₀ hd).mpr (by nlinarith [sq_nonneg y])

/-- The response loss is nonnegative and at most half the squared endpoint defect. -/
theorem chain_response_loss_bounds (n : ℕ) :
    0 ≤ chainResponseLoss n ∧ chainResponseLoss n ≤ eta n ^ 2 / 2 := by
  have hp := eta_pos n
  have hu := eta_le_ninth n
  obtain ⟨hl, hr⟩ := log_remainder_bounds (y := eta n / 2) (by positivity) (by linarith)
  refine ⟨hl, ?_⟩
  dsimp [chainResponseLoss]
  nlinarith

/-- The integer recurrence and logarithmic estimate give the exponential escape witness. -/
theorem chain_response_loss_le_geometric (n : ℕ) :
    chainResponseLoss n ≤ (1 / 2 : ℝ) * (1 / 81 : ℝ) ^ (n + 1) := by
  have hp := eta_pos n
  have hu := eta_le_ninth_pow n
  have hsq : eta n ^ 2 ≤ (1 / (9 : ℝ) ^ (n + 1)) ^ 2 := by
    nlinarith
  calc
    chainResponseLoss n ≤ eta n ^ 2 / 2 := (chain_response_loss_bounds n).2
    _ ≤ (1 / (9 : ℝ) ^ (n + 1)) ^ 2 / 2 := by linarith
    _ = (1 / 2 : ℝ) * (1 / 81 : ℝ) ^ (n + 1) := by
      rw [← _root_.one_div_pow, ← pow_mul, mul_comm (n + 1) 2, pow_mul]
      norm_num
      ring

/-- Real Schur responses retain no uniform positive selector gap at the chosen price. -/
theorem chain_response_selector_gap_refuted :
    ∀ ε : ℝ, 0 < ε →
      ∃ n : ℕ,
        effective n 2 1 ≠ diagonal ![2, 2] ∧
        0 ≤ chainResponseLoss n ∧
        chainResponseLoss n < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (show (1 / 81 : ℝ) < 1 by norm_num)
  refine ⟨n, effective_ne_scalar n 2, (chain_response_loss_bounds n).1, ?_⟩
  apply (chain_response_loss_le_geometric n).trans_lt
  rw [pow_succ]
  have hp : 0 ≤ (1 / 81 : ℝ) ^ n := by positivity
  nlinarith

#print axioms effective_ne_scalar
#print axioms chain_response_loss_bounds
#print axioms chain_response_loss_le_geometric
#print axioms chain_response_selector_gap_refuted

end

end D5.S3.Arith.GoldenResource.ChainResponseSelectorGap
