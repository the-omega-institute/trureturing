/- GID: D5/S3/QuadraticForms/StructuredRankOneDimensionTwoRefutation
   generality: I
   mirror-B: D5/B/S3/QuadraticForms/StructuredRankOneDimensionTwoRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/StructuredRankOneDimensionTwoRefutation.claim; result=D5/S3/QuadraticForms/StructuredRankOneDimensionTwoRefutation.result; claim=D5/S3/QuadraticForms/StructuredRankOneDimensionTwoRefutation.claim
   digest: For n = 2 a continuous structured downdate on a once-punctured interval switches its negative index. -/

import D5.S3.QuadraticForms.StructuredRankOneFamily
import Mathlib.Algebra.Order.Star.Real

/-! Corollary 8 of Ma–Zhang (DOI 10.5281/zenodo.23920598) on MathOverflow 513954, revision 2:
the threshold `n ≥ 3` in Corollary 6 (StructuredRankOneFamily.countable_family for countable and
hence finite punctures) is sharp. `claim` is the conclusion of Corollary 6 for `n = 2` on the
model open 1-simplex `(0, 1)` with one arbitrary point deleted; `result` refutes it, so the
conclusion already fails for one-point, hence finite, deleted sets. On the
interval punctured at `1/2`, take `D = diag(-1, 1)`, `x = (1, 0)` left of the puncture and
`D = diag(1, -1)`, `x = (0, 1)` right of it. Both pieces are locally constant, hence continuous on
the punctured interval; the pivot is `-1` and the downdates are `diag(0, 1)` and `diag(1, 0)`, both
positive semidefinite; but the index of the negative diagonal entry switches.

admission_basis: escape-witness. Escape witness: the public result itself, produced by the
construction (continuity of the two-piece data through the clopen split of the punctured
interval, and the pivot and downdate computations). -/

set_option autoImplicit false
noncomputable section
open Matrix

namespace D5.S3.QuadraticForms.StructuredRankOneDimensionTwoRefutation

open D5.S3.QuadraticForms.StructuredRankOneInertia
open D5.S3.QuadraticForms.StructuredRankOneFamily

/-- The conclusion of Corollary 6 for `n = 2` on the open 1-simplex punctured at any one point. -/
def claim : Prop :=
  ∀ c ∈ openSimplex 1,
    ∀ (d x : ↥(openSimplex 1 \ {c}) → (Fin 2 → ℝ)), Continuous d → Continuous x →
      (∀ y, pivot (diagonal (d y)) (x y) ≠ 0) →
      (∀ y, (downdate (diagonal (d y)) (x y)).PosSemidef) →
      ((∀ y, 0 < pivot (diagonal (d y)) (x y)) ∧ ∀ i y, 0 ≤ d y i) ∨
        ((∀ y, pivot (diagonal (d y)) (x y) < 0) ∧
          ∃! j : Fin 2, (∀ y, d y j < 0) ∧ (∀ i, i ≠ j → ∀ y, 0 ≤ d y i))

/-- The open 1-simplex punctured at its midpoint. -/
private abbrev Y : Type := ↥(openSimplex 1 \ {fun _ => (1 : ℝ) / 2})


private theorem left_clopen : IsClopen {y : Y | y.1 0 < 1 / 2} := by
  constructor
  · have : {y : Y | y.1 0 < 1 / 2}ᶜ = {y : Y | 1 / 2 < y.1 0} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
      constructor
      · intro h
        refine lt_of_le_of_ne h fun he => ?_
        apply y.2.2
        simp only [Set.mem_singleton_iff]
        funext i; fin_cases i; exact he.symm
      · exact le_of_lt
    rw [← isOpen_compl_iff, this]
    exact isOpen_lt continuous_const ((continuous_apply 0).comp continuous_subtype_val)
  · exact isOpen_lt ((continuous_apply 0).comp continuous_subtype_val) continuous_const

private theorem piece_continuous (a b : Fin 2 → ℝ) :
    Continuous fun y : Y => if y.1 0 < 1 / 2 then a else b := by
  refine continuous_const.if ?_ continuous_const
  intro y hy
  rw [left_clopen.frontier_eq] at hy
  exact absurd hy (Set.notMem_empty y)


private def dL : Fin 2 → ℝ := ![-1, 1]
private def xL : Fin 2 → ℝ := ![1, 0]
private def dR : Fin 2 → ℝ := ![1, -1]
private def xR : Fin 2 → ℝ := ![0, 1]

private theorem pivotL : pivot (diagonal dL) xL = -1 := by
  simp [pivot, dL, xL, dotProduct, Fin.sum_univ_two, mulVec, diagonal]
private theorem pivotR : pivot (diagonal dR) xR = -1 := by
  simp [pivot, dR, xR, dotProduct, Fin.sum_univ_two, mulVec, diagonal]

private theorem downL : downdate (diagonal dL) xL = diagonal ![0, 1] := by
  rw [downdate, pivotL]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dL, xL, vecMulVec, mulVec, dotProduct, diagonal]
private theorem downR : downdate (diagonal dR) xR = diagonal ![1, 0] := by
  rw [downdate, pivotR]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dR, xR, vecMulVec, mulVec, dotProduct, diagonal]

private def pL : Y := ⟨fun _ => 1 / 4, by
  refine ⟨⟨fun _ => by norm_num, by simp; norm_num⟩, ?_⟩
  simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 0; norm_num at this⟩

private def pR : Y := ⟨fun _ => 3 / 4, by
  refine ⟨⟨fun _ => by norm_num, by simp; norm_num⟩, ?_⟩
  simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 0; norm_num at this⟩

/-- Corollary 8: the conclusion of Corollary 6 fails for `n = 2` on the open 1-simplex with one
point deleted. -/
theorem result : ¬ claim := by
  intro h
  have hcases := h (fun _ => (1 : ℝ) / 2) ⟨fun _ => by norm_num, by simp; norm_num⟩
    (fun y => if y.1 0 < 1 / 2 then dL else dR) (fun y => if y.1 0 < 1 / 2 then xL else xR)
    (piece_continuous _ _) (piece_continuous _ _)
    (fun y => by split_ifs <;> simp [pivotL, pivotR])
    (fun y => by
      split_ifs
      · rw [downL]; exact PosSemidef.diagonal fun i => by fin_cases i <;> simp
      · rw [downR]; exact PosSemidef.diagonal fun i => by fin_cases i <;> simp)
  have hL : pL.1 0 < 1 / 2 := by simp [pL]; norm_num
  have hR : ¬ pR.1 0 < 1 / 2 := by simp [pR]; norm_num
  rcases hcases with ⟨hpos, -⟩ | ⟨-, j, ⟨hj, -⟩, -⟩
  · have := hpos pL; simp only [hL, ite_true, pivotL] at this; norm_num at this
  · have h1 := hj pL; have h2 := hj pR
    simp only [hL, ite_true] at h1; simp only [hR, ite_false] at h2
    fin_cases j <;> simp [dL, dR] at h1 h2 <;> linarith

end D5.S3.QuadraticForms.StructuredRankOneDimensionTwoRefutation
