/- GID: D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerAffineSquareCollision
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeArithmetic/IntegerAffineSquareCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer affine fibers contain positive natural vectors with unequal square sums. -/

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The three-point construction is the positive variant of CSA Lemma 7. Source coordinates
1,...,s correspond to `Fin s` by `j ↦ j.val + 1`, for columns, vectors and sums alike.
Mathlib supplies integral rank monotonicity, the kernel witness, and the square/cast laws.
The integer strong-rank argument replaces rational rank-nullity and denominator clearing.
This is general unbounded arithmetic (utility: none), with no history interpretation assumed.
-/

set_option autoImplicit false

namespace IntegerAffineSquareCollision

open scoped BigOperators

/-- An arbitrary integer affine map with more columns than rows has two strictly positive
natural inputs in one fiber whose natural sums of coordinate squares differ. -/
theorem exists_pos_nat_affine_fiber_sq_ne (m s : ℕ) (hms : m < s)
    (A : Matrix (Fin m) (Fin s) ℤ) (b : Fin m → ℤ) :
    ∃ u v : Fin s → ℕ, (∀ j, 0 < u j) ∧ (∀ j, 0 < v j) ∧
      (A.mulVec (fun j => (u j : ℤ)) + b = A.mulVec (fun j => (v j : ℤ)) + b) ∧
      ((∑ j, u j ^ 2) ≠ (∑ j, v j ^ 2)) := by
  classical
  let f : (Fin s → ℤ) →ₗ[ℤ] (Fin m → ℤ) := A.mulVecLin
  have hker : f.ker ≠ ⊥ := by
    intro heq
    have hr := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp heq)
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at hr
    exact (Nat.not_le.mpr hms) hr
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hfd : f d = 0 := LinearMap.mem_ker.mp hd
  have hAd : A.mulVec d = 0 := by
    simpa only [f, Matrix.mulVecLin_apply] using hfd
  let z : Fin s → ℤ := fun j => |d j| + 1
  let p : Fin s → ℤ := z + d
  let n : Fin s → ℤ := z - d
  have hz : ∀ j, 1 ≤ z j := by
    intro j
    dsimp [z]
    linarith [abs_nonneg (d j)]
  have hp : ∀ j, 1 ≤ p j := by
    intro j
    change 1 ≤ |d j| + 1 + d j
    linarith [neg_abs_le (d j)]
  have hn : ∀ j, 1 ≤ n j := by
    intro j
    change 1 ≤ |d j| + 1 - d j
    linarith [le_abs_self (d j)]
  have hpimage : A.mulVec p + b = A.mulVec z + b := by
    change f (z + d) + b = f z + b
    rw [map_add]
    change A.mulVec z + A.mulVec d + b = A.mulVec z + b
    rw [hAd, add_zero]
  have hnimage : A.mulVec n + b = A.mulVec z + b := by
    change f (z - d) + b = f z + b
    rw [map_sub]
    change A.mulVec z - A.mulVec d + b = A.mulVec z + b
    rw [hAd, sub_zero]
  let Q : (Fin s → ℤ) → ℤ := fun w => ∑ j, w j ^ 2
  have hQd_nonneg : 0 ≤ Q d := Finset.sum_nonneg fun j _ => sq_nonneg (d j)
  have hQd_ne : Q d ≠ 0 := by
    intro hzero
    apply hd0
    funext j
    exact (Finset.sum_mul_self_eq_zero_iff Finset.univ d).mp
      (by simpa only [Q, pow_two] using hzero) j (Finset.mem_univ j)
  have hQd : 0 < 2 * Q d := by omega
  have hsecond : Q p + Q n - 2 * Q z = 2 * Q d := by
    change (∑ j, (z j + d j) ^ 2) + (∑ j, (z j - d j) ^ 2) -
      2 * (∑ j, z j ^ 2) = 2 * (∑ j, d j ^ 2)
    rw [← Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hselect : ∃ w : Fin s → ℤ, (∀ j, 1 ≤ w j) ∧
      A.mulVec z + b = A.mulVec w + b ∧ Q z ≠ Q w := by
    by_cases hplus : Q z = Q p
    · refine ⟨n, hn, hnimage.symm, ?_⟩
      intro hminus
      rw [← hplus, ← hminus] at hsecond
      omega
    · exact ⟨p, hp, hpimage.symm, hplus⟩
  obtain ⟨w, hw, himage, hsq⟩ := hselect
  let u : Fin s → ℕ := fun j => (z j).toNat
  let v : Fin s → ℕ := fun j => (w j).toNat
  have hu_cast : ∀ j, (u j : ℤ) = z j := fun j =>
    Int.toNat_of_nonneg (le_trans (by decide : (0 : ℤ) ≤ 1) (hz j))
  have hv_cast : ∀ j, (v j : ℤ) = w j := fun j =>
    Int.toNat_of_nonneg (le_trans (by decide : (0 : ℤ) ≤ 1) (hw j))
  have hu_pos : ∀ j, 0 < u j := by
    intro j
    apply Int.natCast_pos.mp
    rw [hu_cast]
    exact lt_of_lt_of_le (by decide : (0 : ℤ) < 1) (hz j)
  have hv_pos : ∀ j, 0 < v j := by
    intro j
    apply Int.natCast_pos.mp
    rw [hv_cast]
    exact lt_of_lt_of_le (by decide : (0 : ℤ) < 1) (hw j)
  have hu_fun : (fun j => (u j : ℤ)) = z := funext hu_cast
  have hv_fun : (fun j => (v j : ℤ)) = w := funext hv_cast
  have hu_sq : ((∑ j, u j ^ 2 : ℕ) : ℤ) = Q z := by
    simp only [Nat.cast_sum, Nat.cast_pow, hu_cast, Q]
  have hv_sq : ((∑ j, v j ^ 2 : ℕ) : ℤ) = Q w := by
    simp only [Nat.cast_sum, Nat.cast_pow, hv_cast, Q]
  refine ⟨u, v, hu_pos, hv_pos, ?_, ?_⟩
  · simpa only [hu_fun, hv_fun] using himage
  · intro heq
    apply hsq
    exact hu_sq.symm.trans ((congrArg (fun k : ℕ => (k : ℤ)) heq).trans hv_sq)

end IntegerAffineSquareCollision
