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
the threshold `n ≥ 3` in Corollary 6 (StructuredRankOneFamily.continuous_family for finite
punctures, countable_family for countable ones) is sharp. `claim` is the conclusion of
Corollary 6 for `n = 2` on the model open 1-simplex `(0, 1)` with some point `c` deleted, in a
weak form implied by both of its alternatives (the pivot is positive everywhere, or one fixed
diagonal entry is negative everywhere); `result` refutes it, so the conclusion fails after
deleting any one point, and in particular is not uniform over finite deleted sets. On the
interval punctured at `c`, take `D = diag(-1, 1)`, `x = (1, 0)` left of the puncture and
`D = diag(1, -1)`, `x = (0, 1)` right of it. Both pieces are locally constant, hence continuous
on the punctured interval; the pivot is `-1` and the downdates are `diag(0, 1)` and
`diag(1, 0)`, both positive semidefinite; but the index of the negative diagonal entry switches.

admission_basis: escape-witness. Escape witness: the public result itself, produced by the
construction (continuity of the two-piece data through the clopen split of the punctured
interval, and the pivot and downdate computations). -/

set_option autoImplicit false
noncomputable section
open Matrix

namespace D5.S3.QuadraticForms.StructuredRankOneDimensionTwoRefutation

open D5.S3.QuadraticForms.StructuredRankOneInertia
open D5.S3.QuadraticForms.StructuredRankOneFamily

/-- For `n = 2`, some one-point deletion of the open 1-simplex satisfies the conclusion of
Corollary 6, in the weak form: the pivot is positive everywhere or a fixed diagonal entry is
negative everywhere. -/
def claim : Prop :=
  ∃ c ∈ openSimplex 1,
    ∀ (d x : ↥(openSimplex 1 \ {c}) → (Fin 2 → ℝ)), Continuous d → Continuous x →
      (∀ y, pivot (diagonal (d y)) (x y) ≠ 0) →
      (∀ y, (downdate (diagonal (d y)) (x y)).PosSemidef) →
      (∀ y, 0 < pivot (diagonal (d y)) (x y)) ∨ ∃ j : Fin 2, ∀ y, d y j < 0

private theorem coord_ne {c : Fin 1 → ℝ} (y : ↥(openSimplex 1 \ {c})) : y.1 0 ≠ c 0 := by
  intro he
  apply y.2.2
  simp only [Set.mem_singleton_iff]
  funext i; fin_cases i; exact he

private theorem left_clopen (c : Fin 1 → ℝ) :
    IsClopen {y : ↥(openSimplex 1 \ {c}) | y.1 0 < c 0} := by
  have hcont : Continuous fun y : ↥(openSimplex 1 \ {c}) => y.1 0 :=
    (continuous_apply 0).comp continuous_subtype_val
  constructor
  · have : {y : ↥(openSimplex 1 \ {c}) | y.1 0 < c 0}ᶜ = {y | c 0 < y.1 0} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
      exact ⟨fun h => lt_of_le_of_ne h (coord_ne y).symm, le_of_lt⟩
    rw [← isOpen_compl_iff, this]
    exact isOpen_lt continuous_const hcont
  · exact isOpen_lt hcont continuous_const

private theorem piece_continuous (c : Fin 1 → ℝ) (a b : Fin 2 → ℝ) :
    Continuous fun y : ↥(openSimplex 1 \ {c}) => if y.1 0 < c 0 then a else b := by
  refine continuous_const.if ?_ continuous_const
  intro y hy
  rw [(left_clopen c).frontier_eq] at hy
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

/-- Corollary 8: for `n = 2`, deleting any one point of the open 1-simplex leaves continuous
data with nonzero pivot and positive semidefinite downdate whose pivot is not positive everywhere
and whose negative diagonal index is not constant. -/
theorem result : ¬ claim := by
  rintro ⟨c, hc, h⟩
  have h0 : 0 < c 0 := hc.1 0
  have h1 : c 0 < 1 := by simpa using hc.2
  have hcases := h (fun y => if y.1 0 < c 0 then dL else dR)
    (fun y => if y.1 0 < c 0 then xL else xR)
    (piece_continuous c _ _) (piece_continuous c _ _)
    (fun y => by split_ifs <;> simp [pivotL, pivotR])
    (fun y => by
      split_ifs
      · rw [downL]; exact PosSemidef.diagonal fun i => by fin_cases i <;> simp
      · rw [downR]; exact PosSemidef.diagonal fun i => by fin_cases i <;> simp)
  let pL : ↥(openSimplex 1 \ {c}) := ⟨fun _ => c 0 / 2, ⟨fun _ => by positivity, by simp; linarith⟩,
    fun he => by have := congrFun he 0; linarith⟩
  let pR : ↥(openSimplex 1 \ {c}) := ⟨fun _ => (1 + c 0) / 2, ⟨fun _ => by positivity,
    by simp; linarith⟩, fun he => by have := congrFun he 0; linarith⟩
  have hL : pL.1 0 < c 0 := by simp [pL]; linarith
  have hR : ¬ pR.1 0 < c 0 := by simp [pR]; linarith
  rcases hcases with hpos | ⟨j, hj⟩
  · have := hpos pL; simp only [hL, ite_true, pivotL] at this; norm_num at this
  · have h1 := hj pL; have h2 := hj pR
    simp only [hL, ite_true] at h1; simp only [hR, ite_false] at h2
    fin_cases j <;> simp [dL, dR] at h1 h2 <;> linarith

end D5.S3.QuadraticForms.StructuredRankOneDimensionTwoRefutation
