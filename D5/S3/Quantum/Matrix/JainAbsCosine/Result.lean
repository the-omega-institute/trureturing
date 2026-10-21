/- GID: D5/S3/Quantum/Matrix/JainAbsCosine/Result
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/JainAbsCosine/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.RingDivision, mathlib/module/Mathlib.Data.Fin.Basic]
   utility: none
   digest: Nonzero nonconstant Fourier modes give exactly double characteristic roots. -/

import D5.S3.Quantum.Matrix.JainAbsCosine.Separation
import D5.S3.Quantum.Matrix.CirculantCharpoly
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Fin.Basic

/-! Fourier factorization and exact multiplicity for the absolute cosine matrix. -/

noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace D5.S3.Quantum.Matrix.JainAbsCosine.Result

open Defs TrigSignChanges Separation
open D5.S3.Quantum.Matrix.CirculantCharpoly

private lemma order_mul_angle (m : ℕ) : (2 * (m : ℝ) + 1) * angle m = Real.pi := by
  unfold angle
  have hn : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private lemma entry_reflection (m k : ℕ) (hk : k ≤ 2 * m + 1) :
    |Real.cos (((2 * m + 1 - k : ℕ) : ℝ) * angle m)| =
      |Real.cos ((k : ℝ) * angle m)| := by
  rw [Nat.cast_sub hk]
  push_cast
  rw [sub_mul, order_mul_angle, Real.cos_pi_sub, abs_neg]

private lemma absCosPow_eq_circulant (m : ℕ) (r : ℝ) :
    absCosPow m r = realCirculant m (fun k => |Real.cos ((k : ℝ) * angle m)| ^ r) := by
  ext a b
  change |Real.cos (((a.val : ℝ) - b.val) * angle m)| ^ r =
    |Real.cos (((a - b).val : ℝ) * angle m)| ^ r
  have hv : ((a - b).val : ℝ) = (a.val : ℝ) - b.val +
      if b ≤ a then 0 else (2 * (m : ℝ) + 1) := by
    exact_mod_cast Fin.intCast_val_sub_eq_sub_add_ite a b
  rw [hv]
  split_ifs with h
  · simp
  · rw [add_mul, order_mul_angle, Real.cos_add_pi, abs_neg]

private lemma cosineValue_eq_modeValue (m j : ℕ) (r : ℝ) :
    cosineValue m (fun k => |Real.cos ((k : ℝ) * angle m)| ^ r) j = modeValue m j r := by
  unfold cosineValue modeValue
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, abs_one, Real.one_rpow]
  congr 2
  apply sum_congr rfl
  intro l hl
  have hc := (cosine_base_bounds (mem_Icc.mp hl).1 (mem_Icc.mp hl).2).1
  rw [abs_of_pos hc]
  have hp : 2 * Real.pi * (j : ℝ) * l / (2 * (m : ℝ) + 1) =
      2 * (j : ℝ) * l * angle m := by
    unfold angle
    ring
  rw [hp, mul_comm]

private theorem absCosPow_charpoly (m : ℕ) (r : ℝ) :
    (absCosPow m r).charpoly = (X - C (modeValue m 0 r)) *
      ∏ j ∈ Icc 1 m, (X - C (modeValue m j r)) ^ 2 := by
  rw [absCosPow_eq_circulant, realCirculant_charpoly]
  · simp_rw [cosineValue_eq_modeValue]
  · intro k hk
    rw [entry_reflection m k (by have := (mem_Icc.mp hk).2; omega)]

/-- Every nonzero characteristic root other than the largest mode has multiplicity two. -/
theorem result : claim := by
  classical
  intro m r μ hm _hr hroot hμ0 htop
  have heval : (μ - modeValue m 0 r) *
      ∏ j ∈ Icc 1 m, (μ - modeValue m j r) ^ 2 = 0 := by
    simpa only [absCosPow_charpoly, IsRoot, eval_mul, eval_prod, eval_pow,
      eval_sub, eval_X, eval_C] using hroot
  have hp : (∏ j ∈ Icc 1 m, (μ - modeValue m j r) ^ 2) = 0 :=
    (mul_eq_zero.mp heval).resolve_left (sub_ne_zero.mpr htop)
  obtain ⟨j, hj, hz⟩ := Finset.prod_eq_zero_iff.mp hp
  have hμj : μ = modeValue m j r := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
  let q : ℝ[X] := (X - C (modeValue m 0 r)) *
    ∏ k ∈ (Icc 1 m).erase j, (X - C (modeValue m k r)) ^ 2
  have hfactor : (absCosPow m r).charpoly = q * (X - C μ) ^ 2 := by
    rw [absCosPow_charpoly, ← Finset.prod_erase_mul (Icc 1 m)
      (fun k => (X - C (modeValue m k r) : ℝ[X]) ^ 2) hj, ← mul_assoc, hμj]
  have hqeval : q.eval μ ≠ 0 := by
    dsimp [q]
    rw [eval_mul, eval_sub, eval_X, eval_C, eval_prod]
    apply mul_ne_zero
    · rw [hμj]
      exact sub_ne_zero.mpr (ne_of_lt (modeValue_lt_top hm
        (mem_Icc.mp hj).1 (mem_Icc.mp hj).2 r))
    · apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      rw [eval_pow, eval_sub, eval_X, eval_C]
      apply pow_ne_zero
      apply sub_ne_zero.mpr
      intro he
      have hkj : k = j := modeValue_injective_nonzero
        (mem_Icc.mp (mem_erase.mp hk).2).1 (mem_Icc.mp (mem_erase.mp hk).2).2
        (mem_Icc.mp hj).1 (mem_Icc.mp hj).2 r
        (he.symm.trans hμj) (he ▸ hμ0)
      exact (mem_erase.mp hk).1 hkj
  have hq : q ≠ 0 := by
    intro he
    exact hqeval (by simp [he])
  rw [hfactor, rootMultiplicity_mul_X_sub_C_pow hq,
    rootMultiplicity_eq_zero hqeval, zero_add]

end D5.S3.Quantum.Matrix.JainAbsCosine.Result
