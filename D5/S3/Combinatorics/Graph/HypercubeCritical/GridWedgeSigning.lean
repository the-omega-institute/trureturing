/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSigning
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSigning
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity, mathlib/module/Mathlib.Data.Fintype.BigOperators]
   utility: none
   digest: Explicit Huang switching of the grid-wedge support for every d at least two. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeComponent
import D5.S3.Combinatorics.Graph.HypercubeCritical.GrayGridComponent
import Batteries.Tactic.OpenPrivate

/-! The literal TRUE-row grid-wedge support is balanced in Huang's fixed FALSE-prefix signing. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeSigning

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeComponent
open BalancedCriticalSpectrum (Q IsSwitching)
open private rowPrefix switchSign switchSign_unit gridPrefix_flip sign_lower_edge from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeComponent
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_flip_prefix from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GrayGridComponent
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

open Classical in
/-- The finite realization of the literal TRUE-row support. -/
def supportFinset {d : ℕ} (hd : 2 ≤ d) : Finset (GridWedgeComponent.Vertex d) :=
  Finset.univ.filter (fun x => x ∈ support hd)

private def theta {n : ℕ} (x : Q n) : ℝ :=
  ∏ k : Fin n, if x k = true then (-1 : ℝ) ^ k.val else 1

/-- A Huang switching obtained from the TRUE-prefix support switching and the
vertex potential converting TRUE-prefix to the repository's FALSE-prefix matrix. -/
def switching {d : ℕ} (hd : 2 ≤ d) (x : GridWedgeComponent.Vertex d) : ℝ :=
  theta x * (switchSign hd x : ℝ)

private theorem theta_flip {n : ℕ} (x : Q n) (q : Fin n) :
    theta x * theta (BalancedCriticalSpectrum.flip x q) = (-1 : ℝ) ^ q.val := by
  classical
  unfold theta
  rw [← Finset.prod_mul_distrib]
  let f := fun k : Fin n =>
    (if x k = true then (-1 : ℝ) ^ k.val else 1) *
      (if BalancedCriticalSpectrum.flip x q k = true then (-1 : ℝ) ^ k.val else 1)
  change ∏ k, f k = _
  rw [Finset.prod_eq_single q]
  · cases hq : x q <;> simp [f, BalancedCriticalSpectrum.flip, hq]
  · intro k _ hk
    have hcoord : BalancedCriticalSpectrum.flip x q k = x k :=
      Function.update_of_ne hk _ _
    rcases neg_one_pow_eq_or ℝ k.val with h | h <;>
      by_cases hx : x k = true <;> simp [f, hcoord, hx, h]
  · simp

private theorem gridFlip_eq_matrixFlip {d : ℕ} (x : GridWedgeComponent.Vertex d) (i j : Fin d) :
    GridWedgeComponent.flip x i j =
      BalancedCriticalSpectrum.flip x (finProdFinEquiv (i, j)) := by
  classical
  funext q
  by_cases hq : q = finProdFinEquiv (i, j) <;>
    simp [GridWedgeComponent.flip, BalancedCriticalSpectrum.flip, hq]

private theorem row_major_lt {d : ℕ} (a b i j : Fin d) :
    finProdFinEquiv (a, b) < finProdFinEquiv (i, j) ↔
      a < i ∨ a = i ∧ b < j := by
  classical
  change b.val + d * a.val < j.val + d * i.val ↔ _
  have hb := b.isLt
  have hj := j.isLt
  constructor
  · intro h
    by_cases ha : a < i
    · exact Or.inl ha
    · right
      have hia : i.val ≤ a.val := by simpa using (not_lt.mp ha)
      have he : a = i := by
        by_contra hn
        have hai : i.val + 1 ≤ a.val := by
          have := fun h => hn (Fin.ext h)
          omega
        have hm := Nat.mul_le_mul_left d hai
        nlinarith
      exact ⟨he, by subst a; simpa using h⟩
  · rintro (h | ⟨rfl, h⟩)
    · have hm := Nat.mul_le_mul_left d (show a.val + 1 ≤ i.val by simpa using h)
      nlinarith
    · simpa using h

private theorem prod_true_sign {α : Type} (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (∏ k ∈ s, if p k then (-1 : ℝ) else 1) = (-1 : ℝ) ^ (s.filter p).card := by
  classical
  rw [Finset.prod_ite]
  simp

private theorem true_prefix_grid {d : ℕ} (x : GridWedgeComponent.Vertex d) (i j : Fin d) :
    (∏ q : Fin (d * d),
      if q < finProdFinEquiv (i, j) ∧ x q = true then (-1 : ℝ) else 1) =
        (gridEdgeSign x i j : ℝ) := by
  classical
  rw [← Equiv.prod_comp finProdFinEquiv, Fintype.prod_prod_type]
  have hr (a : Fin d) :
      (∏ b : Fin d,
        if finProdFinEquiv (a, b) < finProdFinEquiv (i, j) ∧
          x (finProdFinEquiv (a, b)) = true then (-1 : ℝ) else 1) =
        (-1 : ℝ) ^ (if a < i then (gridRow x a).card
          else if a = i then ((gridRow x i).filter (fun b => b < j)).card else 0) := by
    rw [prod_true_sign]
    congr 1
    by_cases ha : a < i
    · simp only [ite_eq_left ha]
      congr 1
      ext b
      simp [gridRow, row_major_lt, ha]
    · by_cases he : a = i
      · subst a
        simp only [lt_self_iff_false, ite_false, ite_true]
        congr 1
        ext b
        simp [gridRow, row_major_lt, and_comm]
      · simp only [ite_eq_right ha, ite_eq_right he]
        apply Finset.card_eq_zero.mpr
        ext b
        simp [row_major_lt, ha, he]
  simp_rw [hr]
  rw [Finset.prod_pow_eq_pow_sum]
  have he (a : Fin d) :
      (if a < i then (gridRow x a).card
        else if a = i then ((gridRow x i).filter (fun b => b < j)).card else 0) =
      (if a < i then (gridRow x a).card else 0) +
        (if a = i then ((gridRow x i).filter (fun b => b < j)).card else 0) := by
    by_cases ha : a < i
    · have hn : a ≠ i := ne_of_lt ha
      simp [ha, hn]
    · simp [ha]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hs : (∑ a : Fin d, if a < i then (gridRow x a).card else 0) =
      rowPrefix x i := by
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp
  rw [hs]
  simp [gridEdgeSign, gridPrefix]

private theorem matrix_true_conversion {d : ℕ} (x : GridWedgeComponent.Vertex d) (i j : Fin d) :
    huangMatrix (d * d) x (GridWedgeComponent.flip x i j) =
      theta x * theta (GridWedgeComponent.flip x i j) *
        (gridEdgeSign x i j : ℝ) := by
  classical
  rw [gridFlip_eq_matrixFlip, matrix_flip_prefix, theta_flip, ← true_prefix_grid]
  have he (q : Fin (d * d)) :
      (if q < finProdFinEquiv (i, j) ∧ x q = false then (-1 : ℝ) else 1) =
        (if q < finProdFinEquiv (i, j) then (-1 : ℝ) else 1) *
          (if q < finProdFinEquiv (i, j) ∧ x q = true then (-1 : ℝ) else 1) := by
    by_cases hq : q < finProdFinEquiv (i, j) <;> cases x q <;> simp [hq]
  simp_rw [he]
  rw [Finset.prod_mul_distrib, prod_true_sign]
  have hf : (Finset.univ.filter (fun q => q < finProdFinEquiv (i, j))) =
      Finset.Iio (finProdFinEquiv (i, j)) := by ext q; simp
  rw [hf, Fin.card_Iio]

private theorem true_switching_edge {d : ℕ} (hd : 2 ≤ d)
    {x : GridWedgeComponent.Vertex d} (hx : x ∈ support hd) (i j : Fin d)
    (hy : GridWedgeComponent.flip x i j ∈ support hd) :
    gridEdgeSign x i j = switchSign hd x * switchSign hd (GridWedgeComponent.flip x i j) := by
  classical
  rcases hx with hu | hl | ht
  · have hw := upperPattern_weight hd hu
    have hylower : lowerDoublePattern hd (GridWedgeComponent.flip x i j) ∨
        lowerTransversalPattern hd (GridWedgeComponent.flip x i j) := by
      rcases hy with hyu | hyl | hyt
      · have hw' := upperPattern_weight hd hyu
        cases hb : x (finProdFinEquiv (i, j))
        · have he := gridWeight_flip_false x i j hb; omega
        · have he := gridWeight_flip_true x i j hb; omega
      · exact Or.inl hyl
      · exact Or.inr hyt
    have hback : GridWedgeComponent.flip (GridWedgeComponent.flip x i j) i j = x := by
      rw [gridFlip_eq_matrixFlip, gridFlip_eq_matrixFlip, BalancedCriticalSpectrum.flip_flip]
    have hs := sign_lower_edge hd (GridWedgeComponent.flip x i j) hylower i j
      (by rw [hback]; exact Or.inl hu)
    simpa [gridEdgeSign, gridPrefix_flip, hback, mul_comm] using hs
  · exact sign_lower_edge hd x (Or.inl hl) i j hy
  · exact sign_lower_edge hd x (Or.inr ht) i j hy

private theorem theta_unit {n : ℕ} (x : Q n) : theta x = 1 ∨ theta x = -1 := by
  classical
  have he (k : Fin n) : (if x k = true then (-1 : ℝ) ^ k.val else 1) =
      (-1 : ℝ) ^ (if x k = true then k.val else 0) := by
    by_cases hk : x k = true <;> simp [hk]
  unfold theta
  simp_rw [he]
  rw [Finset.prod_pow_eq_pow_sum]
  exact neg_one_pow_eq_or ℝ _

private theorem switching_unit {d : ℕ} (hd : 2 ≤ d) (x : GridWedgeComponent.Vertex d) :
    switching hd x = 1 ∨ switching hd x = -1 := by
  classical
  rcases theta_unit x with ht | ht <;>
    rcases switchSign_unit hd x with hs | hs <;> simp [switching, ht, hs]

private theorem switching_edge {d : ℕ} (hd : 2 ≤ d) {x : GridWedgeComponent.Vertex d}
    (hx : x ∈ support hd) (i j : Fin d) (hy : GridWedgeComponent.flip x i j ∈ support hd) :
    huangMatrix (d * d) x (GridWedgeComponent.flip x i j) =
      switching hd x * switching hd (GridWedgeComponent.flip x i j) := by
  classical
  rw [matrix_true_conversion, true_switching_edge hd hx i j hy]
  push_cast
  simp only [switching]
  ring

/-- The constructed support is switching-balanced for Huang's actual matrix. -/
theorem support_isSwitching {d : ℕ} (hd : 2 ≤ d) :
    IsSwitching (supportFinset hd) (switching hd) := by
  classical
  constructor
  · intro x _hx
    exact switching_unit hd x
  · intro x hx y hy hxy
    obtain ⟨q, rfl⟩ := adjacent_exists_flip hxy
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective q
    have hy' : GridWedgeComponent.flip x i j ∈ support hd := by
      simpa [gridFlip_eq_matrixFlip] using (Finset.mem_filter.mp hy).2
    exact switching_edge hd ((Finset.mem_filter.mp hx).2) i j hy'

end D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeSigning
