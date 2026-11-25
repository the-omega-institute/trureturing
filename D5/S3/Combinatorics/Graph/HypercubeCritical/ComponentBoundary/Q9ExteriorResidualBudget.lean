/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ExteriorResidualBudget
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ExteriorResidualBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Weighted exterior residuals bound the number of remaining vertices of a balanced cube support. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

/-! For Hong–Wu–Xia Problem 2, partial signs on the first shells of a
balanced cubic component prescribe exterior cancellation demands. A
nonnegative weighting of those demands and a bound on each possible
remaining column give a lower bound on the completion size. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ExteriorResidualBudget

open Finset
attribute [local instance] Classical.propDecidable
open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsSwitching switchingVector switching_sq ambient_eigenvector)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private theorem unit_entry_abs {n : ℕ} {x y : Q n}
    (h : (hypercube n).Adj x y) : |huangMatrix n x y| = 1 := by
  have he := SupportedEigenSaturation.matrix_sq_of_adj h
  rcases sq_eq_one_iff.mp he with h | h <;> simp [h]

private theorem exterior_sum {C : Finset (Q 9)} {s : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C s) {r : Q 9} (hrC : r ∉ C) :
    ∑ x ∈ C, huangMatrix 9 r x * s x = 0 := by
  classical
  have h := congrFun (ambient_eigenvector (d := 3) C s hr hs) r
  change (∑ x, huangMatrix 9 r x * switchingVector C s x) =
    3 * switchingVector C s r at h
  simpa only [switchingVector, if_neg hrC, mul_zero, mul_ite, ← Finset.sum_filter,
    filter_mem_eq_inter, univ_inter] using h

/-- A weighted sum of exterior cancellation demands of a partial switching
is bounded by the total weighted incidence of the remaining support. This
makes exterior norms into lower bounds for completion budgets. -/
theorem weighted_exterior_residual_budget {C P R : Finset (Q 9)} {s : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C s) (hP : P ⊆ C) (hR : Disjoint R C)
    (w : Q 9 → ℝ) (hw : ∀ r ∈ R, 0 ≤ w r) (capacity : ℝ)
    (hcol : ∀ y ∈ C \ P, ∑ r ∈ R, (if (hypercube 9).Adj r y then w r else 0) ≤ capacity) :
    (∑ r ∈ R, w r * |∑ x ∈ P, huangMatrix 9 r x * s x|) ≤
      capacity * ((C \ P).card : ℝ) := by
  classical
  let T := C \ P
  have hpartition : Disjoint P T := by
    exact disjoint_left.mpr (fun x hx ht => (mem_sdiff.mp ht).2 hx)
  have hunion : P ∪ T = C := Finset.union_sdiff_of_subset hP
  have hcancel (r : Q 9) (hrR : r ∈ R) :
      (∑ x ∈ P, huangMatrix 9 r x * s x) =
        -(∑ y ∈ T, huangMatrix 9 r y * s y) := by
    have h := exterior_sum hr hs (fun hc => disjoint_left.mp hR hrR hc)
    rw [← hunion, sum_union hpartition] at h
    exact eq_neg_of_add_eq_zero_left h
  have hentry (r y : Q 9) (hy : y ∈ T) :
      |huangMatrix 9 r y * s y| = if (hypercube 9).Adj r y then 1 else 0 := by
    have hyC := (mem_sdiff.mp hy).1
    by_cases ha : (hypercube 9).Adj r y
    · rw [if_pos ha, abs_mul, unit_entry_abs ha]
      rcases hs.1 y hyC with h | h <;> simp [h]
    · rw [if_neg ha, SupportedEigenSaturation.matrix_eq_zero_of_not_adj ha, zero_mul, abs_zero]
  calc
    _ ≤ ∑ r ∈ R, w r * ∑ y ∈ T, (if (hypercube 9).Adj r y then 1 else 0) := by
      apply sum_le_sum
      intro r h
      apply mul_le_mul_of_nonneg_left _ (hw r h)
      rw [hcancel r h, abs_neg]
      calc
        _ ≤ ∑ y ∈ T, |huangMatrix 9 r y * s y| := abs_sum_le_sum_abs _ _
        _ = _ := sum_congr rfl fun y hy => hentry r y hy
    _ = ∑ y ∈ T, ∑ r ∈ R, (if (hypercube 9).Adj r y then w r else 0) := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro r _
      split_ifs <;> simp
    _ ≤ ∑ y ∈ T, capacity := sum_le_sum hcol
    _ = _ := by simp [T, mul_comm]

#print axioms weighted_exterior_residual_budget

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ExteriorResidualBudget
