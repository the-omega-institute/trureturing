/- GID: D5/S3/ArithSums/GiniStationaryTest/Stationary
   generality: I
   mirror-B: D5/B/S3/ArithSums/GiniStationaryTest/Stationary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Deriv.Add, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Inv, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Mul, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Pow, mathlib/module/Mathlib.Analysis.Convex.SpecificFunctions.Deriv]
   utility: none
   digest: Normalized stationary tuples pass the comparison test for two fixed Gini parameters. -/

import D5.S3.ArithSums.GiniStationaryTest.Defs
import D5.S3.Quantum.Matrix.AlternativeMeanLinearization
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-! Positive stationary levels and their normalized moments. -/

noncomputable section
open scoped BigOperators
namespace D5.S3.ArithSums.GiniStationaryTest.Stationary
open Defs

/-- The characteristic derivatives for the two parameter pairs. -/
theorem chiDeriv_parameters (z : ℝ) (hz : 0 < z) :
    chiDeriv 1 0 z = 1 ∧ chiDeriv 2 (-1) z = (2 * z + (z ^ 2)⁻¹) / 3 := by
  constructor
  · have hf : chi 1 0 = fun z : ℝ => z - 1 := by
      funext z
      simp [chi]
    rw [chiDeriv, hf]
    simpa using ((hasDerivAt_id z).sub_const 1).deriv
  · have hf : chi 2 (-1) = fun z : ℝ => (z ^ 2 - z⁻¹) / 3 := by
      funext z
      norm_num [chi, Real.rpow_two, Real.rpow_neg_one]
    rw [chiDeriv, hf]
    convert (((hasDerivAt_id z).pow 2).sub (hasDerivAt_inv hz.ne')).div_const 3 |>.deriv using 1 <;>
      simp

/-- Distinct positive points on a stationary level satisfy a quadratic product relation. -/
private lemma level_pair {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : 2 * a + (a ^ 2)⁻¹ = 2 * b + (b ^ 2)⁻¹) :
    a = b ∨ a + b = 2 * (a * b) ^ 2 := by
  have he : (a - b) * (2 * (a * b) ^ 2 - (a + b)) = 0 := by
    field_simp [ha.ne', hb.ne'] at h
    nlinarith [h]
  rcases mul_eq_zero.mp he with he | he
  · exact Or.inl (sub_eq_zero.mp he)
  · exact Or.inr (by linarith)

/-- A positive level of the stationary function contains at most two points. -/
private lemma level_two_values {a b z : ℝ} (ha : 0 < a) (hb : 0 < b) (hz : 0 < z)
    (hab : a ≠ b)
    (hba : 2 * a + (a ^ 2)⁻¹ = 2 * b + (b ^ 2)⁻¹)
    (hza : 2 * a + (a ^ 2)⁻¹ = 2 * z + (z ^ 2)⁻¹) :
    z = a ∨ z = b := by
  by_contra hnot
  have hza' : (z⁻¹) ^ 3 = -2 + (2 * a + (a ^ 2)⁻¹) * z⁻¹ := by
    field_simp [ha.ne', hz.ne'] at hza ⊢
    nlinarith [hza]
  have hba' : (b⁻¹) ^ 3 = -2 + (2 * a + (a ^ 2)⁻¹) * b⁻¹ := by
    field_simp [ha.ne', hb.ne'] at hba ⊢
    nlinarith [hba]
  have haa' : (a⁻¹) ^ 3 = -2 + (2 * a + (a ^ 2)⁻¹) * a⁻¹ := by
    field_simp [ha.ne']
    ring
  have hne_za : z⁻¹ ≠ a⁻¹ := by
    intro h
    apply hnot
    left
    exact inv_inj.mp h
  have hne_zb : z⁻¹ ≠ b⁻¹ := by
    intro h
    apply hnot
    right
    exact inv_inj.mp h
  have hne_ab : a⁻¹ ≠ b⁻¹ := by
    intro h
    exact hab (inv_inj.mp h)
  have hfalse :=
    D5.S3.Quantum.Matrix.AlternativeMeanLinearization.affine_three
      (fun x : ℝ => x ^ (3 : ℕ))
      (Or.inl ((strictConvexOn_pow (by norm_num : 2 ≤ (3 : ℕ))).subset
        Set.Ioi_subset_Ici_self (convex_Ioi 0)))
      (-(2 : ℝ)) (2 * a + (a ^ 2)⁻¹) (a⁻¹) (b⁻¹) (z⁻¹)
      (inv_pos.mpr ha) (inv_pos.mpr hb) (inv_pos.mpr hz)
      hne_ab hne_za.symm hne_zb.symm haa' hba' hza'
  exact hfalse.elim

private lemma stationary_sum_strict {n : ℕ} (u : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (hs : ∑ i, u i = n)
    (hg : ∀ i j, 2 * u i + (u i ^ 2)⁻¹ = 2 * u j + (u j ^ 2)⁻¹)
    (hd : ¬ ∀ i, u i = 1) :
    (∑ i, (u i)⁻¹) < ∑ i, (u i) ^ 2 := by
  classical
  have hs0 : ∑ i, (u i - 1) = 0 := by simp [Finset.sum_sub_distrib, hs]
  have hne : ∃ i ∈ (Finset.univ : Finset (Fin n)), u i - 1 ≠ 0 := by
    push Not at hd
    obtain ⟨i, hi⟩ := hd
    exact ⟨i, Finset.mem_univ _, sub_ne_zero.mpr hi⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_neg_of_sum_zero_of_exists_nonzero _ hs0 hne
  obtain ⟨j, _, hj⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero _ hs0 hne
  let a := u i
  let b := u j
  have ha : 0 < a := hu i
  have hb : 0 < b := hu j
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hb1 : 1 < b := by dsimp [b]; linarith
  have hab : a ≠ b := ne_of_lt (ha1.trans hb1)
  have hS : a + b = 2 * (a * b) ^ 2 :=
    (level_pair ha hb (hg i j)).resolve_left hab
  have hvals : ∀ k, u k = a ∨ u k = b :=
    fun k => level_two_values ha hb (hu k) hab (hg i j) (hg i k)
  have hsq : ∀ k, (u k) ^ 2 = (a + b) * u k - a * b := by
    intro k
    rcases hvals k with h | h <;> rw [h] <;> ring
  have hinv : ∀ k, (u k)⁻¹ = ((a + b) - u k) / (a * b) := by
    intro k
    rcases hvals k with h | h <;> rw [h] <;> field_simp <;> ring
  have hsum_sq : ∑ k, (u k) ^ 2 = (n : ℝ) * (a + b - a * b) := by
    simp_rw [hsq]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs]
    simp
    ring
  have hsum_inv : ∑ k, (u k)⁻¹ = (n : ℝ) * (a + b - 1) / (a * b) := by
    simp_rw [hinv]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hs]
    simp
    ring
  have hP : 1 < a * b := by
    have hv : 0 < (1 - a) * (b - 1) := mul_pos (by linarith) (by linarith)
    have hp : 0 < a * b := mul_pos ha hb
    by_contra! hn
    have hc := mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ 2 * (a * b) + 1 by positivity)
    nlinarith [hS]
  rw [hsum_inv, hsum_sq]
  apply (div_lt_iff₀ (mul_pos ha hb)).mpr
  have hdiff : (a + b - a * b) * (a * b) - (a + b - 1) =
      (a * b - 1) * ((1 - a) * (b - 1)) := by ring
  have hp := mul_pos (sub_pos.mpr hP)
    (mul_pos (show 0 < 1 - a by linarith) (show 0 < b - 1 by linarith))
  have hn : (0 : ℝ) < n := by
    have hidx := i.isLt
    exact_mod_cast (show 0 < n by omega)
  nlinarith [mul_pos hn hp]

/-- Every positive normalized stationary tuple passes the second Gini mean test. -/
theorem stationaryTest_one_zero_two_negOne (n : ℕ) (hn : 1 ≤ n) :
    ∀ u : Fin n → ℝ, (∀ i, 0 < u i) → giniMean 1 0 u = 1 →
      (∃ ρ : ℝ, ∀ k, chiDeriv 2 (-1) (u k) + ρ * chiDeriv 1 0 (u k) = 0) →
      1 ≤ giniMean 2 (-1) u := by
  intro u hu hnorm hstationary
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  by_cases hd : ∀ i, u i = 1
  · simp [giniMean, GiniMeanEndpointComparison.giniMean, hd, hn0]
  have hmean : giniMean 1 0 u = (∑ i, u i) / n := by
    simp [giniMean, GiniMeanEndpointComparison.giniMean]
  have hsum : ∑ i, u i = n := by
    rw [hmean] at hnorm
    exact (div_eq_one_iff_eq hn0).mp hnorm
  obtain ⟨ρ, hρ⟩ := hstationary
  have hg : ∀ i j, 2 * u i + (u i ^ 2)⁻¹ = 2 * u j + (u j ^ 2)⁻¹ := by
    intro i j
    have hi := hρ i
    have hj := hρ j
    rw [(chiDeriv_parameters (u i) (hu i)).1,
      (chiDeriv_parameters (u i) (hu i)).2] at hi
    rw [(chiDeriv_parameters (u j) (hu j)).1,
      (chiDeriv_parameters (u j) (hu j)).2] at hj
    linarith
  have hsum_inv_pos : 0 < ∑ i, (u i)⁻¹ := by
    apply Finset.sum_pos
    · intro i _
      exact inv_pos.mpr (hu i)
    · exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hratio : 1 < (∑ i, (u i) ^ 2) / (∑ i, (u i)⁻¹) := by
    apply (one_lt_div hsum_inv_pos).mpr
    exact stationary_sum_strict u hu hsum hg hd
  have hformula : giniMean 2 (-1) u =
      ((∑ i, (u i) ^ 2) / (∑ i, (u i)⁻¹)) ^ (1 / 3 : ℝ) := by
    norm_num [giniMean, GiniMeanEndpointComparison.giniMean, Real.rpow_two,
      Real.rpow_neg_one]
  rw [hformula]
  exact (Real.one_lt_rpow hratio (by norm_num : (0 : ℝ) < 1 / 3)).le

end D5.S3.ArithSums.GiniStationaryTest.Stationary
