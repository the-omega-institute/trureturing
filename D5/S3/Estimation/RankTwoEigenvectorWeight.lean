/- GID: D5/S3/Estimation/RankTwoEigenvectorWeight
   generality: G
   mirror-B: D5/B/S3/Estimation/RankTwoEigenvectorWeight
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Rank-two positive diagonal forms turn a trace gap into an eigenvector weight gap. -/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Real.Basic

/-! Spectral coordinates of a positive sum of two rank-one forms. -/

set_option autoImplicit false

open Matrix Finset
open scoped BigOperators

namespace D5.S3.Estimation.RankTwoEigenvectorWeight

/-- A two-column factorization and a strict half-trace estimate force a larger weight
away from any maximal diagonal entry. -/
theorem weight_gap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ e s : ι → ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hdiag : ∀ i j, (if i = j then μ i else 0) =
      a * (s i * s j) + b * (e i * e j))
    (hgap : 2 * (∑ j, μ j * e j ^ 2) < (∑ j, μ j) * ∑ j, e j ^ 2)
    (i : ι) (htop : ∀ j, μ j ≤ μ i) :
    ∃ j, j ≠ i ∧ e i ^ 2 < e j ^ 2 := by
  classical
  have hself : ∀ j, μ j = a * s j ^ 2 + b * e j ^ 2 := by
    intro j
    simpa only [ite_true, ← sq] using hdiag j j
  have hμ : ∀ j, 0 ≤ μ j := fun j => by rw [hself]; positivity
  have hzero : ∀ j, μ j = 0 → e j = 0 := by
    intro j hj
    have heq := hself j
    rw [hj] at heq
    have ha0 := mul_nonneg ha.le (sq_nonneg (s j))
    have hb0 := mul_nonneg hb.le (sq_nonneg (e j))
    have hz : b * e j ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hb.ne')
  let x : Matrix ι (Fin 2) ℝ := fun j t => if t = 0 then a * s j else b * e j
  let y : Matrix (Fin 2) ι ℝ := fun t j => if t = 0 then s j else e j
  have hfactor : diagonal μ = x * y := by
    ext j k
    change (if j = k then μ j else 0) = ∑ t : Fin 2, x j t * y t k
    simp only [Fin.sum_univ_two]
    norm_num [x, y, mul_assoc]
    exact hdiag j k
  let t := univ.filter (fun j => μ j ≠ 0)
  have hcard : t.card ≤ 2 := by
    have hr : (diagonal μ).rank ≤ 2 := by
      rw [hfactor]
      exact (rank_mul_le_left x y).trans (by simpa using rank_le_card_width x)
    simpa only [rank_diagonal, Fintype.card_subtype, t] using hr
  have hex : ∃ j, j ≠ i ∧ μ j ≠ 0 := by
    by_contra h
    have hz : ∀ j, j ≠ i → μ j = 0 := by
      intro j hji
      by_contra hj
      exact h ⟨j, hji, hj⟩
    have hm : ∑ j, μ j = μ i := by
      apply sum_eq_single i
      · intro j _ hji; exact hz j hji
      · simp
    have he : ∑ j, e j ^ 2 = e i ^ 2 := by
      apply sum_eq_single i
      · intro j _ hji; rw [hzero j (hz j hji)]; norm_num
      · simp
    have hme : ∑ j, μ j * e j ^ 2 = μ i * e i ^ 2 := by
      apply sum_eq_single i
      · intro j _ hji; rw [hz j hji, zero_mul]
      · simp
    rw [hm, he, hme] at hgap
    nlinarith only [hgap, mul_nonneg (hμ i) (sq_nonneg (e i))]
  obtain ⟨j, hji, hjμ⟩ := hex
  have hiμ : μ i ≠ 0 := ne_of_gt ((lt_of_le_of_ne (hμ j) hjμ.symm).trans_le (htop j))
  have hi : i ∈ t := mem_filter.mpr ⟨mem_univ _, hiμ⟩
  have hj : j ∈ t.erase i := mem_erase.mpr ⟨hji, mem_filter.mpr ⟨mem_univ _, hjμ⟩⟩
  have hrest : (t.erase i).card ≤ 1 := by rw [card_erase_of_mem hi]; omega
  have hz : ∀ k, k ≠ i → k ≠ j → μ k = 0 := by
    intro k hki hkj
    by_contra hk
    have hkt : k ∈ t.erase i := mem_erase.mpr ⟨hki, mem_filter.mpr ⟨mem_univ _, hk⟩⟩
    exact hkj (card_le_one.mp hrest k hkt j hj)
  have hsum : ∀ f : ι → ℝ, (∀ k, k ≠ i → k ≠ j → f k = 0) →
      ∑ k, f k = f i + f j := by
    intro f hf
    rw [← sum_subset (subset_univ ({i, j} : Finset ι))]
    · exact sum_pair hji.symm
    · intro k _ hk
      simp only [mem_insert, mem_singleton, not_or] at hk
      exact hf k hk.1 hk.2
  have hm := hsum μ hz
  have he := hsum (fun k => e k ^ 2) (fun k hki hkj => by rw [hzero k (hz k hki hkj)]; norm_num)
  have hme := hsum (fun k => μ k * e k ^ 2)
    (fun k hki hkj => by rw [hz k hki hkj, zero_mul])
  rw [hm, he, hme] at hgap
  refine ⟨j, hji, ?_⟩
  by_contra h
  have hd := mul_nonneg (sub_nonneg.mpr (htop j)) (sub_nonneg.mpr (le_of_not_gt h))
  nlinarith only [hgap, hd]

end D5.S3.Estimation.RankTwoEigenvectorWeight
