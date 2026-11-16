/- GID: D5/S3/Quantum/Algebra/SemidefiniteCoefficientKernelCheck
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/SemidefiniteCoefficientKernelCheck
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive semidefinite coefficient forms have trivial kernel on independent matrix families. -/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Positive semidefinite coefficient-kernel exclusion

The coefficient map is injective on positive semidefinite matrices when the
matrix family is complex-linearly independent. The diagonal entries reduce
the claim to the positive-semidefinite zero-quadratic-form lemma.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Algebra.SemidefiniteCoefficientKernelCheck

theorem exact_check {a b k : ℕ}
    (X : Fin k → Matrix (Fin a) (Fin b) ℂ)
    (hX : LinearIndependent ℂ X)
    (T : Matrix (Fin k) (Fin k) ℂ) (hT : T.PosSemidef)
    (hPhi : (∑ r, ∑ s, T r s • ((X r)ᴴ * X s)) = 0) : T = 0 := by
  classical
  have hquad (j : Fin b) :
      ∑ i : Fin a, star (fun r => X r i j) ⬝ᵥ
        (T *ᵥ (fun r => X r i j)) = 0 := by
    have hd := congrArg (fun A : Matrix (Fin b) (Fin b) ℂ => A j j) hPhi
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply] at hd
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    calc
      _ = ∑ r : Fin k, ∑ i : Fin a, ∑ s : Fin k,
          star (X r i j) * (T r s * X s i j) := by
        rw [Finset.sum_comm]
      _ = ∑ r : Fin k, ∑ s : Fin k, ∑ i : Fin a,
          star (X r i j) * (T r s * X s i j) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.sum_comm]
      _ = ∑ r : Fin k, ∑ s : Fin k, T r s * ∑ i : Fin a,
          (star (X r i j) * X s i j) := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hd
  have hker (i : Fin a) (j : Fin b) : T *ᵥ (fun r => X r i j) = 0 := by
    apply hT.dotProduct_mulVec_zero_iff.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin a))) =>
        hT.dotProduct_mulVec_nonneg (fun r => X r i j))).mp (hquad j) i
          (Finset.mem_univ i)
  ext r s
  apply Fintype.linearIndependent_iff.mp hX (fun s => T r s) ?_ s
  ext i j
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.zero_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] using
      congrFun (hker i j) r

#print axioms exact_check

end D5.S3.Quantum.Algebra.SemidefiniteCoefficientKernelCheck
