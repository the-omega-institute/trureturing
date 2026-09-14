/- GID: D5/S3/Analytic/Interpolation/HermiteMomentBounds
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/HermiteMomentBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive finite coordinates give a positive lower Hermite node and are bounded above by the upper moment node. -/

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset

namespace D5.S3.Analytic.Interpolation.HermiteMomentBounds

/-- The two nodes determined by the mean and total squared deviation satisfy
positivity of the lower node and an upper bound for every coordinate. -/
theorem hermite_moment_bounds {k : ℕ} (hk : 2 ≤ k) (x : Fin k → ℝ)
    (hx : ∀ i, 0 < x i) :
    let μ := (∑ i, x i) / (k : ℝ)
    let V := ∑ i, (x i - μ)^2
    let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
    0 < μ - r ∧ ∀ i, x i ≤ μ + ((k : ℝ) - 1) * r := by
  let : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  let μ := (∑ i, x i) / (k : ℝ)
  let V := ∑ i, (x i - μ)^2
  let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
  change 0 < μ - r ∧ ∀ i, x i ≤ μ + ((k : ℝ) - 1) * r
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hkm : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := mul_pos hkpos hkm
  have hsum : ∑ i, x i = (k : ℝ) * μ := by
    dsimp [μ]
    field_simp
  have hμ : 0 < μ := div_pos (sum_pos (fun i _ => hx i) univ_nonempty) hkpos
  have hV : 0 ≤ V := sum_nonneg (fun i _ => sq_nonneg (x i - μ))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r^2 = V / ((k : ℝ) * ((k : ℝ) - 1)) :=
    Real.sq_sqrt (div_nonneg hV hden.le)
  have hVr : V = (k : ℝ) * ((k : ℝ) - 1) * r^2 := by
    rw [hrsq]
    field_simp
  have hcenter : ∑ i, (x i - μ) = 0 := by
    rw [sum_sub_distrib]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hvariance : V = (∑ i, (x i)^2) - (k : ℝ) * μ^2 := by
    dsimp [V]
    simp_rw [sub_sq]
    rw [sum_add_distrib, sum_sub_distrib]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← sum_mul]
    rw [← mul_sum, hsum]
    ring
  have hstrict : (∑ i, (x i)^2) < (∑ i, x i)^2 := by
    have hxi : ∀ i, x i < ∑ j, x j := by
      intro i
      obtain ⟨j, hji⟩ := exists_ne i
      have herase : 0 < ∑ l ∈ univ.erase i, x l := by
        apply sum_pos (fun l _ => hx l)
        exact ⟨j, mem_erase.mpr ⟨hji, mem_univ j⟩⟩
      have heq := sum_erase_add univ x (mem_univ i)
      linarith
    calc
      (∑ i, (x i)^2) < ∑ i, x i * (∑ j, x j) := by
        apply sum_lt_sum_of_nonempty univ_nonempty
        intro i _
        simpa only [pow_two] using mul_lt_mul_of_pos_left (hxi i) (hx i)
      _ = (∑ i, x i)^2 := by rw [← sum_mul, pow_two]
  have hVlt : V < (k : ℝ) * ((k : ℝ) - 1) * μ^2 := by
    rw [hsum] at hstrict
    nlinarith [hvariance]
  have hrlt : r < μ := by
    apply (Real.sqrt_lt' hμ).mpr
    exact (div_lt_iff₀ hden).mpr (by nlinarith [hVlt])
  refine ⟨sub_pos.mpr hrlt, ?_⟩
  intro i
  have herasesum : ∑ j ∈ univ.erase i, (x j - μ) = -(x i - μ) := by
    have heq := sum_erase_add univ (fun j => x j - μ) (mem_univ i)
    linarith
  have herasesq : ∑ j ∈ univ.erase i, (x j - μ)^2 = V - (x i - μ)^2 := by
    have heq := sum_erase_add univ (fun j => (x j - μ)^2) (mem_univ i)
    change _ = V at heq
    linarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := univ.erase i) (f := fun j => x j - μ)
  rw [herasesum, herasesq, neg_sq] at hcs
  have hcard : ((univ.erase i).card : ℝ) = (k : ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ i)]
    simp only [card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  rw [hcard] at hcs
  have hsq : (x i - μ)^2 ≤ ((k : ℝ) - 1)^2 * r^2 := by
    have he : (k : ℝ) * (x i - μ)^2 ≤ ((k : ℝ) - 1) * V := by nlinarith [hcs]
    rw [hVr] at he
    have hm : (k : ℝ) * (x i - μ)^2 ≤
        (k : ℝ) * (((k : ℝ) - 1)^2 * r^2) := by nlinarith [he]
    exact (mul_le_mul_iff_right₀ hkpos).mp hm
  have huppernonneg : 0 ≤ ((k : ℝ) - 1) * r := mul_nonneg hkm.le hr
  nlinarith [sq_nonneg (x i - μ - ((k : ℝ) - 1) * r)]

end D5.S3.Analytic.Interpolation.HermiteMomentBounds
