/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickCornerCriterion
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickCornerCriterion
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Singular common-corner optimality and its exact commutator criterion. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickCornerOptimization

/-! Positive-overlap optimality on a singular contraction's actual common corner. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open D5.S3.Quantum.Divergence.MaximalHockeyStickCorner
open D5.S3.Quantum.Divergence.MaximalHockeyStickCornerWeight
open D5.S3.Quantum.Divergence.MaximalHockeyStickCornerOptimization
open D5.S3.Quantum.Divergence.MaximalHockeyStickThreshold
open D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickCornerCriterion

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem diagonal_optimal_iff (d : n → ℝ) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (W : Matrix n n ℂ)
    (hW : (W.submatrix (fun i : {i // 0 < d i ∧ d i < 1} => i.val) Subtype.val).PosDef)
    (t : ℝ) (ht : 0 < t) :
    let D := diagonal (fun i => (d i : ℂ))
    let Y := diagonal (fun i => ((min (d i) (t * (1 - d i)) : ℝ) : ℂ))
    let P := diagonal (fun i => if 0 < d i ∧ d i < 1 then (1 : ℂ) else 0)
    (∀ X ∈ positiveOverlaps D (t • (1 - D)), (W * X).trace.re ≤ (W * Y).trace.re) ↔
      diagonal (fun i => ((max (d i - t * (1 - d i)) 0 : ℝ) : ℂ)) * (P * W * P) *
        diagonal (fun i => ((max (t * (1 - d i) - d i) 0 : ℝ) : ℂ)) = 0 := by
  classical
  dsimp only
  have hred := diagonal_optimization_reduction d hd W t ht.le
  dsimp only at hred
  rw [hred]
  let I := {i // 0 < d i ∧ d i < 1}
  let D : Matrix I I ℂ := diagonal (fun i => (d i.val : ℂ))
  let Y : Matrix I I ℂ := diagonal (fun i => ((min (d i.val) (t * (1 - d i.val)) : ℝ) : ℂ))
  let V : Matrix I I ℂ := W.submatrix Subtype.val Subtype.val
  have hY : Y.PosDef := Matrix.PosDef.diagonal (fun i => by
    exact_mod_cast lt_min i.property.1 (mul_pos ht (sub_pos.mpr i.property.2)))
  have hD : D.IsHermitian := (Matrix.PosSemidef.diagonal (fun i => by
    change (0 : ℂ) ≤ _
    exact_mod_cast (hd i.val).1)).isHermitian
  have hfeas := diagonal_feasible (fun i : I => d i.val) (fun i => hd i.val) t ht.le
  have hc : (∀ X ∈ positiveOverlaps D (t • (1 - D)),
      (V * X).trace.re ≤ (V * Y).trace.re) ↔
      (D - Y) * V * (t • (1 - D) - Y) = 0 := by
    simpa only [positiveOverlaps, Set.mem_setOf_eq, and_imp] using
      weighted_overlap_optimal_iff D (t • (1 - D)) V Y hD
      ((Matrix.isHermitian_one.sub hD).smul (IsSelfAdjoint.all t)) hW hY
      hfeas.2.1 hfeas.2.2
  have hrA : D - Y = diagonal (fun i : I => ((max (d i.val - t * (1 - d i.val)) 0 : ℝ) : ℂ)) := by
    dsimp only [D, Y]
    rw [Matrix.diagonal_sub]
    congr 1
    funext i
    rcases le_total (d i.val) (t * (1 - d i.val)) with h | h <;>
      simp [min_eq_left, min_eq_right, h, sub_nonpos.mpr h, sub_nonneg.mpr h]
  have hrB : t • (1 - D) - Y =
      diagonal (fun i : I => ((max (t * (1 - d i.val) - d i.val) 0 : ℝ) : ℂ)) := by
    have he : t • (1 - D) = diagonal (fun i : I => ((t * (1 - d i.val) : ℝ) : ℂ)) := by
      dsimp only [D]
      rw [← Matrix.diagonal_one, Matrix.diagonal_sub, ← Matrix.diagonal_smul]
      apply congrArg (fun f : I → ℂ => diagonal f)
      funext i
      simp [Complex.real_smul]
    rw [he]
    dsimp only [Y]
    rw [Matrix.diagonal_sub]
    congr 1
    funext i
    rcases le_total (d i.val) (t * (1 - d i.val)) with h | h <;>
      simp [min_eq_left, min_eq_right, h, sub_nonpos.mpr h, sub_nonneg.mpr h]
  have hc' := hc
  rw [hrA, hrB] at hc'
  simp only [Matrix.submatrix_diagonal _ _ Subtype.val_injective] 
  change (∀ X ∈ positiveOverlaps D (t • (1 - D)),
    (V * X).trace.re ≤ (V * Y).trace.re) ↔ _
  rw [hc']
  constructor
  · intro h
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply]
    by_cases hi : 0 < d i ∧ d i < 1
    · by_cases hj : 0 < d j ∧ d j < 1
      · have he := congrArg (fun M : Matrix I I ℂ => M ⟨i, hi⟩ ⟨j, hj⟩) h
        simpa only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply,
          V, Matrix.submatrix_apply, if_pos hi, if_pos hj, one_mul, mul_one] using he
      · simp [hj]
    · simp [hi]
  · intro h
    ext i j
    have he := congrArg (fun M : Matrix n n ℂ => M i.val j.val) h
    simpa only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply,
      V, Matrix.submatrix_apply, if_pos i.property, if_pos j.property, one_mul, mul_one] using he

end D5.S3.Quantum.Divergence.MaximalHockeyStickCornerCriterion
