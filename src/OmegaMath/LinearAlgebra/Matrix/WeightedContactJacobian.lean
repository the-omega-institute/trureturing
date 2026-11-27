import OmegaBuild.Commands
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul

/-! The homogeneous equations of weighted contact optimization. -/

compile_only_with_mathlib

namespace Omega.WeightedContactJacobian

open Matrix
open scoped BigOperators Matrix

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq k]

/-- A weighted Gram term vanishes in the homogeneous saddle equations
exactly when the vector is orthogonal to all the columns of its factor. -/
theorem reduced_kernel_iff (A : Matrix m n R) (B : Matrix m k R) (d : k → R)
    (hd : ∀ i, 0 < d i) (u : n → R) (y : m → R) :
    (A *ᵥ u + B *ᵥ (diagonal d *ᵥ (Bᵀ *ᵥ y)) = 0 ∧ Aᵀ *ᵥ y = 0) ↔
      A *ᵥ u = 0 ∧ Aᵀ *ᵥ y = 0 ∧ Bᵀ *ᵥ y = 0 := by
  constructor
  · rintro ⟨hmoment, hcontact⟩
    have hyA : y ᵥ* A = 0 := by
      simpa only [transpose_transpose, hcontact] using vecMul_transpose Aᵀ y
    have hyB : y ᵥ* B = Bᵀ *ᵥ y := by
      simpa only [transpose_transpose] using vecMul_transpose Bᵀ y
    have hweighted : (Bᵀ *ᵥ y) ⬝ᵥ (diagonal d *ᵥ (Bᵀ *ᵥ y)) = 0 := by
      have hpair := congrArg (fun v : m → R => y ⬝ᵥ v) hmoment
      simpa only [dotProduct_add, dotProduct_mulVec, hyA, hyB,
        zero_dotProduct, dotProduct_zero, zero_add] using hpair
    have hsum : ∑ i, (Bᵀ *ᵥ y) i * (d i * (Bᵀ *ᵥ y) i) = 0 := by
      simpa only [dotProduct, mulVec_diagonal] using hweighted
    have htangent : Bᵀ *ᵥ y = 0 := by
      funext i
      have hnonneg (j : k) :
          0 ≤ (Bᵀ *ᵥ y) j * (d j * (Bᵀ *ᵥ y) j) := by
        rw [← mul_assoc, mul_comm ((Bᵀ *ᵥ y) j) (d j), mul_assoc]
        exact mul_nonneg (hd j).le (mul_self_nonneg _)
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp
        hsum i (Finset.mem_univ i)
      simpa only [mul_eq_zero, (hd i).ne', false_or, or_self, Pi.zero_apply] using hi
    exact ⟨by simpa only [htangent, mulVec_zero, add_zero] using hmoment,
      hcontact, htangent⟩
  · rintro ⟨hmoment, hcontact, htangent⟩
    exact ⟨by simp only [hmoment, htangent, mulVec_zero, add_zero], hcontact⟩

end Omega.WeightedContactJacobian
