/- GID: D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionLower
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reciprocal-degree charging bounds rectangular weak two-resolving sets. -/

import D5.S3.Combinatorics.Graph.HammingWeakTwoMetricDimensionCore
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace D5.S3.Combinatorics.Graph.HammingWeakTwoMetricDimension

open scoped BigOperators

private theorem reciprocal_fiber_sum {E V : Type*} [DecidableEq E]
    [Fintype V] [DecidableEq V] (S : Finset E) (f : E → V)
    (hpos : ∀ v, 0 < (S.filter (fun e => f e = v)).card) :
    (∑ e ∈ S, (1 : ℚ) / ((S.filter (fun e' => f e' = f e)).card : ℚ)) =
      Fintype.card V := by
  rw [← Finset.sum_fiberwise' S f (fun v => (1 : ℚ) / ((S.filter (fun e => f e = v)).card : ℚ))]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have each (v : V) :
      ((S.filter (fun e => f e = v)).card : ℚ) *
        (1 / ((S.filter (fun e => f e = v)).card : ℚ)) = 1 := by
    exact mul_one_div_cancel (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hpos v)))
  simp_rw [each]
  simp

private theorem reciprocal_pair_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : 3 ≤ a + b) : (1 : ℚ) / a + 1 / b ≤ 3 / 2 := by
  by_cases h : a = 1
  · subst a
    have hb' : (2 : ℚ) ≤ b := by exact_mod_cast (show 2 ≤ b by omega)
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 2) hb'
    norm_num at *
    linarith
  by_cases h' : b = 1
  · subst b
    have ha' : (2 : ℚ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 2) ha'
    norm_num at *
    linarith
  have ha' : (2 : ℚ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
  have hb' : (2 : ℚ) ≤ b := by exact_mod_cast (show 2 ≤ b by omega)
  have h1 := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 2) ha'
  have h2 := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 2) hb'
  norm_num at *
  linarith

private theorem reciprocal_pair_strong_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 ≤ a + b) : (1 : ℚ) / a + 1 / b ≤ 4 / 3 := by
  by_cases h : a = 1
  · subst a
    have hb' : (3 : ℚ) ≤ b := by exact_mod_cast (show 3 ≤ b by omega)
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 3) hb'
    norm_num at *
    linarith
  by_cases h' : b = 1
  · subst b
    have ha' : (3 : ℚ) ≤ a := by exact_mod_cast (show 3 ≤ a by omega)
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 3) ha'
    norm_num at *
    linarith
  have ha' : (2 : ℚ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
  have hb' : (2 : ℚ) ≤ b := by exact_mod_cast (show 2 ≤ b by omega)
  have h1 := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 2) ha'
  have h2 := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 2) hb'
  norm_num at *
  linarith

/-- A bipartite incidence set with no isolated vertices and endpoint-degree sum
at least six on disjoint edges has at least two thirds as many edges as vertices. -/
theorem bipartite_degree_charging {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (S : Finset (I × J))
    (hrow : ∀ i, 0 < (S.filter (fun e => e.1 = i)).card)
    (hcol : ∀ j, 0 < (S.filter (fun e => e.2 = j)).card)
    (hdisj : ∀ e ∈ S, ∀ e' ∈ S, e.1 ≠ e'.1 → e.2 ≠ e'.2 →
      6 ≤ (S.filter (fun w => w.1 = e.1)).card +
        (S.filter (fun w => w.2 = e.2)).card +
        (S.filter (fun w => w.1 = e'.1)).card +
        (S.filter (fun w => w.2 = e'.2)).card)
    (hsize : 6 ≤ Fintype.card I + Fintype.card J) :
    2 * (Fintype.card I + Fintype.card J) ≤ 3 * S.card := by
  let g := fun i => (S.filter (fun e => e.1 = i)).card
  let h := fun j => (S.filter (fun e => e.2 = j)).card
  let q := fun e : I × J => (1 : ℚ) / g e.1 + 1 / h e.2
  have total : (∑ e ∈ S, q e) = (Fintype.card I + Fintype.card J : ℕ) := by
    dsimp only [q, g, h]
    rw [Finset.sum_add_distrib, reciprocal_fiber_sum S Prod.fst hrow,
      reciprocal_fiber_sum S Prod.snd hcol]
    simp
  by_cases isolated : ∃ e ∈ S, g e.1 = 1 ∧ h e.2 = 1
  · obtain ⟨e, he, hge, hhe⟩ := isolated
    have disjoint (e' : I × J) (he' : e' ∈ S) (hne : e' ≠ e) :
        e.1 ≠ e'.1 ∧ e.2 ≠ e'.2 := by
      constructor
      · intro hh
        have hcard : (S.filter (fun w => w.1 = e.1)).card ≤ 1 := by
          change g e.1 ≤ 1
          omega
        have heq := Finset.card_le_one.mp hcard e
          (Finset.mem_filter.mpr ⟨he, rfl⟩) e'
          (Finset.mem_filter.mpr ⟨he', hh.symm⟩)
        exact hne heq.symm
      · intro hh
        have hcard : (S.filter (fun w => w.2 = e.2)).card ≤ 1 := by
          change h e.2 ≤ 1
          omega
        have heq := Finset.card_le_one.mp hcard e
          (Finset.mem_filter.mpr ⟨he, rfl⟩) e'
          (Finset.mem_filter.mpr ⟨he', hh.symm⟩)
        exact hne heq.symm
    have others : ∑ e' ∈ S.erase e, q e' ≤ (S.erase e).card * (4 / 3 : ℚ) := by
      calc
        _ ≤ ∑ _e' ∈ S.erase e, (4 / 3 : ℚ) := by
          apply Finset.sum_le_sum
          intro e' he'
          obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp he'
          obtain ⟨hr, hc⟩ := disjoint e' hmem hne
          have hs := hdisj e he e' hmem hr hc
          change 6 ≤ g e.1 + h e.2 + g e'.1 + h e'.2 at hs
          exact reciprocal_pair_strong_bound _ _ (hrow _) (hcol _) (by omega)
        _ = _ := by simp
    have split : ∑ e' ∈ S, q e' = q e + ∑ e' ∈ S.erase e, q e' := by
      exact (Finset.add_sum_erase _ _ he).symm
    have qe : q e = 2 := by norm_num [q, hge, hhe]
    have card : (S.erase e).card + 1 = S.card := Finset.card_erase_add_one he
    have cardQ : ((S.erase e).card : ℚ) + 1 = (S.card : ℚ) := by exact_mod_cast card
    have sizeQ : (6 : ℚ) ≤ (Fintype.card I + Fintype.card J : ℕ) := by
      exact_mod_cast hsize
    have bound : (2 : ℚ) * (Fintype.card I + Fintype.card J : ℕ) ≤ 3 * S.card := by
      rw [split, qe] at total
      linarith
    exact_mod_cast bound
  · have each (e : I × J) (he : e ∈ S) : q e ≤ (3 / 2 : ℚ) := by
      apply reciprocal_pair_bound _ _ (hrow _) (hcol _)
      change 3 ≤ g e.1 + h e.2
      by_contra hh
      have hg := hrow e.1
      have hc := hcol e.2
      change 0 < g e.1 at hg
      change 0 < h e.2 at hc
      apply isolated
      exact ⟨e, he, by omega, by omega⟩
    have hs : ∑ e ∈ S, q e ≤ (S.card : ℚ) * (3 / 2) := by
      calc
        _ ≤ ∑ _e ∈ S, (3 / 2 : ℚ) := Finset.sum_le_sum each
        _ = _ := by simp
    rw [total] at hs
    have bound : (2 : ℚ) * (Fintype.card I + Fintype.card J : ℕ) ≤ 3 * S.card := by
      linarith
    exact_mod_cast bound

/-- The sharp candidate is a lower bound for every weak two-resolving set. -/
theorem lower_bound {n m : ℕ} (S : Finset (Fin n × Fin m))
    (hS : IsWeakResolving 2 S) (hn : 4 ≤ n) (hnm : n < m) :
    min ((2 * (n + m) + 2) / 3) (2 * n - 2) ≤ S.card := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let j0 : Fin m := ⟨0, by omega⟩
  by_cases er : ∃ i, rowDegree S i = 0
  · obtain ⟨i, hi⟩ := er
    have hb : ∑ i' ∈ Finset.univ.erase i, 2 ≤
        ∑ i' ∈ Finset.univ.erase i, rowDegree S i' := by
      apply Finset.sum_le_sum
      intro i' hi'
      have hd := row_pair_degree S hS i i' j0 (Finset.mem_erase.mp hi').1.symm
      omega
    have hs : ∑ i' ∈ Finset.univ.erase i, rowDegree S i' = S.card := by
      have hsum := Finset.add_sum_erase Finset.univ (rowDegree S) (Finset.mem_univ i)
      rw [hi, zero_add, sum_rowDegree] at hsum
      exact hsum
    have hc : (Finset.univ.erase i).card = n - 1 := by simp
    simp only [Finset.sum_const, Nat.nsmul_eq_mul, hc] at hb
    rw [hs] at hb
    have hbound : 2 * n - 2 ≤ S.card := by omega
    exact (min_le_right _ _).trans hbound
  by_cases ec : ∃ j, colDegree S j = 0
  · obtain ⟨j, hj⟩ := ec
    have hb : ∑ j' ∈ Finset.univ.erase j, 2 ≤
        ∑ j' ∈ Finset.univ.erase j, colDegree S j' := by
      apply Finset.sum_le_sum
      intro j' hj'
      have hd := col_pair_degree S hS i0 j j' (Finset.mem_erase.mp hj').1.symm
      omega
    have hs : ∑ j' ∈ Finset.univ.erase j, colDegree S j' = S.card := by
      have hsum := Finset.add_sum_erase Finset.univ (colDegree S) (Finset.mem_univ j)
      rw [hj, zero_add, sum_colDegree] at hsum
      exact hsum
    have hc : (Finset.univ.erase j).card = m - 1 := by simp
    simp only [Finset.sum_const, Nat.nsmul_eq_mul, hc] at hb
    rw [hs] at hb
    have hbound : 2 * n - 2 ≤ S.card := by omega
    exact (min_le_right _ _).trans hbound
  have hr : ∀ i, 0 < rowDegree S i := by
    intro i
    have : rowDegree S i ≠ 0 := fun h => er ⟨i, h⟩
    omega
  have hc : ∀ j, 0 < colDegree S j := by
    intro j
    have : colDegree S j ≠ 0 := fun h => ec ⟨j, h⟩
    omega
  have hb := bipartite_degree_charging S hr hc
    (fun e he e' he' hi hj =>
      disjoint_landmark_degree S hS e.1 e'.1 e.2 e'.2 he he' hi hj)
    (by simp only [Fintype.card_fin]; omega)
  simp only [Fintype.card_fin] at hb
  have hceil : (2 * (n + m) + 2) / 3 ≤ S.card := by omega
  exact (min_le_left _ _).trans hceil

end D5.S3.Combinatorics.Graph.HammingWeakTwoMetricDimension
