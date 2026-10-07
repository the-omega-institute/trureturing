/- GID: D5/S3/Combinatorics/OddIndependence/OddGrid
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OddIndependence/OddGrid
   mirror-E: none(waiver:open-grid-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Basic]
   utility: none
   digest: Dense independent square-grid sets contain a full four-neighbour cross. -/

import D5.S3.Combinatorics.OddIndependence.OddGridCertificate
import D5.S3.Combinatorics.OddIndependence.OddGridCounting
import D5.S3.Combinatorics.OddIndependence.OddGridPadding
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.OddIndependence.OddGrid

open Finset OddGridDefs OddGridPadding

/-- An affirmative answer to Problem 29, with the explicit sequence `ε n = 4 / n`. -/
theorem result : OddGridDefs.claim := by
  classical
  refine ⟨fun n => 4 / (n : ℝ), tendsto_const_div_atTop_nhds_zero_nat 4, ?_⟩
  intro n S hn hi hd
  by_contra hc
  have hb (x y : ℕ) : padded S x y = true ↔
      ∃ v ∈ S, v.1.val + 2 = x ∧ v.2.val + 2 = y := by
    simp [padded, mem_image, Prod.mk.injEq]
  have hs (x y : ℕ) (h : padded S x y = true) :
      2 ≤ x ∧ x < n + 2 ∧ 2 ≤ y ∧ y < n + 2 := by
    obtain ⟨v, _, rfl, rfl⟩ := (hb x y).mp h
    have hx := v.1.isLt
    have hy := v.2.isLt
    omega
  have hind (x y : ℕ) :
      (padded S x y = true → padded S (x + 1) y = false) ∧
      (padded S x y = true → padded S x (y + 1) = false) := by
    constructor
    · intro h
      cases he : padded S (x + 1) y with
      | false => rfl
      | true =>
        obtain ⟨v, hv, hvx, hvy⟩ := (hb x y).mp h
        obtain ⟨w, hw, hwx, hwy⟩ := (hb (x + 1) y).mp he
        have ha : (grid n).Adj v w := by
          simp only [grid, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]
          left
          constructor
          · left; omega
          · apply Fin.ext; omega
        exact False.elim (hi hv hw ((grid n).ne_of_adj ha) ha)
    · intro h
      cases he : padded S x (y + 1) with
      | false => rfl
      | true =>
        obtain ⟨v, hv, hvx, hvy⟩ := (hb x y).mp h
        obtain ⟨w, hw, hwx, hwy⟩ := (hb x (y + 1)).mp he
        have ha : (grid n).Adj v w := by
          simp only [grid, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]
          right
          constructor
          · left; omega
          · apply Fin.ext; omega
        exact False.elim (hi hv hw ((grid n).ne_of_adj ha) ha)
  have hcross (x y : ℕ) : ¬ (padded S x (y + 1) = true ∧
      padded S (x + 1) y = true ∧ padded S (x + 1) (y + 2) = true ∧
      padded S (x + 2) (y + 1) = true) := by
    intro h
    exact hc (cross_of_padded S x y h)
  have hbound := OddGridCertificate.certificate_bound n (padded S) hs hind hcross
  rw [OddGridCounting.ninefold_count n (padded S) hs] at hbound
  let T := S.image (fun v => (v.1.val + 2, v.2.val + 2))
  have hsub : T ⊆ (range (n + 2)) ×ˢ (range (n + 2)) := by
    intro p hp
    obtain ⟨v, _, rfl⟩ := mem_image.mp hp
    simp only [mem_product, mem_range]
    constructor <;> omega
  have ht : ((range (n + 2)) ×ˢ (range (n + 2))).filter (· ∈ T) = T := by
    ext p
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have hcard : T.card = S.card := by
    apply card_image_of_injective
    intro v w h
    have he := Prod.mk.inj h
    apply Prod.ext <;> apply Fin.ext <;> omega
  have hcount : (∑ x ∈ range (n + 2), ∑ y ∈ range (n + 2),
      (if padded S x y then (1 : ℤ) else 0)) = S.card := by
    change (∑ x ∈ range (n + 2), ∑ y ∈ range (n + 2),
      (if decide ((x, y) ∈ T) then (1 : ℤ) else 0)) = S.card
    simp only [decide_eq_true_eq]
    rw [← sum_product (range (n + 2)) (range (n + 2))
      (fun p => if p ∈ T then (1 : ℤ) else 0)]
    rw [← sum_filter]
    simp [ht, hcard]
  rw [hcount] at hbound
  have hreal : 8 * (S.card : ℝ) ≤ 3 * ((n : ℝ) + 2) ^ 2 := by
    have hr : (8 : ℝ) * (9 * (S.card : ℝ)) ≤ 27 * ((n : ℝ) + 2) ^ 2 := by
      exact_mod_cast hbound
    nlinarith
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnzero : (n : ℝ) ≠ 0 := by linarith
  have heq : ((3 / 8 : ℝ) + 4 / (n : ℝ)) * (n : ℝ) ^ 2 =
      3 / 8 * (n : ℝ) ^ 2 + 4 * (n : ℝ) := by
    field_simp [hnzero]
  rw [heq] at hd
  nlinarith

#print axioms result

end D5.S3.Combinatorics.OddIndependence.OddGrid
