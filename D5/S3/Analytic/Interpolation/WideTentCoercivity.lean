/- GID: D5/S3/Analytic/Interpolation/WideTentCoercivity
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/WideTentCoercivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centered prefix energies control finite complex coefficient energies. -/

import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Quantitative helpers for a wide triangular Gram form. The finite difference
estimate uses arbitrary complex coefficients and retains both endpoint terms. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators
open Finset Matrix

namespace D5.S3.Analytic.Interpolation.WideTentCoercivity

/-- The prefix before the index `k`. -/
def partialSum (c : ℕ → ℂ) (k : ℕ) : ℂ := ∑ i ∈ range k, c i

private lemma normSq_sub_le (z w : ℂ) :
    Complex.normSq (z - w) ≤ 2 * Complex.normSq z + 2 * Complex.normSq w := by
  have h := Complex.normSq_nonneg (z + w)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im] at h ⊢
  nlinarith

private lemma path_difference_energy_bound (z : ℕ → ℂ) (N : ℕ) :
    (∑ i ∈ range N, Complex.normSq (z (i + 1) - z i)) ≤
      2 * Complex.normSq (z 0) + 2 * Complex.normSq (z N) +
        4 * ∑ k ∈ Ico 1 N, Complex.normSq (z k) := by
  by_cases hN : N = 0
  · subst N
    simp only [range_zero, sum_empty, Ico_self, mul_zero, add_zero]
    positivity
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  have hbound := sum_le_sum (s := range N) (fun i _ => normSq_sub_le (z (i + 1)) (z i))
  have hleft : (∑ i ∈ range N, Complex.normSq (z i)) =
      Complex.normSq (z 0) + ∑ k ∈ Ico 1 N, Complex.normSq (z k) :=
    sum_range_eq_add_Ico (fun k => Complex.normSq (z k)) hN0
  have hright : (∑ i ∈ range N, Complex.normSq (z (i + 1))) =
      (∑ k ∈ Ico 1 N, Complex.normSq (z k)) + Complex.normSq (z N) := by
    calc
      (∑ i ∈ range N, Complex.normSq (z (i + 1))) =
          ∑ i ∈ Ico 1 (N + 1), Complex.normSq (z i) := by
        simpa only [range_eq_Ico, zero_add] using
          (sum_Ico_add' (fun i => Complex.normSq (z i)) 0 N 1)
      _ = _ := sum_Ico_succ_top (Nat.one_le_iff_ne_zero.mpr hN)
        (fun i => Complex.normSq (z i))
  simp only [sum_add_distrib, ← mul_sum] at hbound
  rw [hleft, hright] at hbound
  linarith

/-- A finite coefficient family is controlled by its total mass and centered
interior prefixes. This is a consumed finite-difference estimate. -/
theorem centered_prefix_energy_bound (c : ℕ → ℂ) (N : ℕ) :
    (∑ i ∈ range N, Complex.normSq (c i)) ≤
      Complex.normSq (partialSum c N) +
        4 * ∑ k ∈ Ico 1 N, Complex.normSq (partialSum c k - partialSum c N / 2) := by
  let S := partialSum c N
  let z : ℕ → ℂ := fun k => partialSum c k - S / 2
  have hincr (i : ℕ) : z (i + 1) - z i = c i := by
    dsimp [z, partialSum]
    rw [sum_range_succ]
    ring
  have hzero : z 0 = -S / 2 := by simp [z, partialSum, S]; ring
  have hlast : z N = S / 2 := by dsimp [z, S]; ring
  have hend : 2 * Complex.normSq (z 0) + 2 * Complex.normSq (z N) =
      Complex.normSq S := by
    rw [hzero, hlast]
    norm_num [Complex.normSq_div, Complex.normSq_neg]
    ring
  have h := path_difference_energy_bound z N
  simp_rw [hincr] at h
  rw [hend] at h
  exact h

/-- Positive gaps and a wide endpoint coefficient turn centered-prefix control
into the required `g/2` lower bound. The two remaining inputs for a tent matrix
are its ordered-gap identity and the finite reindexing of its nodes. -/
theorem centered_gap_coercivity (c : ℕ → ℂ) (N : ℕ) (d : ℕ → ℝ)
    {g D L : ℝ} (hg : 0 < g) (hgD : g ≤ D) (hDL : D ≤ L)
    (hd : ∀ k ∈ range (N + 1), g ≤ d k) :
    (g / 2) * (∑ i ∈ range (N + 2), Complex.normSq (c i)) ≤
      (L - D / 2) * Complex.normSq (partialSum c (N + 2)) +
        2 * ∑ k ∈ range (N + 1), d k *
          Complex.normSq (partialSum c (k + 1) - partialSum c (N + 2) / 2) := by
  let S := partialSum c (N + 2)
  let Y : ℕ → ℝ := fun k => Complex.normSq (partialSum c (k + 1) - S / 2)
  have hshift : (∑ k ∈ Ico 1 (N + 2),
      Complex.normSq (partialSum c k - S / 2)) = ∑ k ∈ range (N + 1), Y k := by
    simpa only [range_eq_Ico, zero_add, Nat.add_assoc] using
      (sum_Ico_add' (fun k => Complex.normSq (partialSum c k - S / 2)) 0 (N + 1) 1).symm
  have hc := centered_prefix_energy_bound c (N + 2)
  change (∑ i ∈ range (N + 2), Complex.normSq (c i)) ≤
    Complex.normSq S + 4 * ∑ k ∈ Ico 1 (N + 2),
      Complex.normSq (partialSum c k - S / 2) at hc
  rw [hshift] at hc
  have hweighted : g * (∑ k ∈ range (N + 1), Y k) ≤
      ∑ k ∈ range (N + 1), d k * Y k := by
    rw [mul_sum]
    exact sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right (hd k hk)
      (Complex.normSq_nonneg _))
  have hbase : (g / 2) * Complex.normSq S ≤ (L - D / 2) * Complex.normSq S :=
    mul_le_mul_of_nonneg_right (by linarith) (Complex.normSq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hc (show 0 ≤ g / 2 by positivity)
  change (g / 2) * (∑ i ∈ range (N + 2), Complex.normSq (c i)) ≤
    (L - D / 2) * Complex.normSq S + 2 * ∑ k ∈ range (N + 1), d k * Y k
  nlinarith

end D5.S3.Analytic.Interpolation.WideTentCoercivity
