/- GID: D5/S3/Resource/CompositeConeProperness
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exhibit witnesses proving both inclusions in the composite cone chain are proper. -/

/- The import closure consists of `CompositeCones` (generality `G`) and its
umbrella `Mathlib` import (generality `G`).  In particular, this module does not
import the generality-`I` module `CompositeConeDuality`.

Library-search receipt (2026-08-13): pinned mathlib provides
`Matrix.trace_kronecker`, `Matrix.mul_kronecker_mul`,
`Matrix.posSemidef_iff_eq_sum_vecMulVec`, and
`Matrix.PosSemidef.re_dotProduct_nonneg`.  It has no theorem named
`Matrix.PosSemidef.trace_mul_nonneg`; the needed real trace inequality is proved
below from the last two declarations.  A repository-wide search found no
properness theorem or SWAP/singlet witness for `separableCone` or
`blockPositive` beyond `CompositeCones` and `CompositeConeDuality`. -/

import D5.S3.Resource.CompositeCones

namespace D5.S3.Resource.CompositeConeProperness

open D5.S3.Resource.CompositeCones
open scoped ComplexOrder
open scoped Kronecker

/-- The exchange operator on two two-dimensional factors. -/
def swapMatrix : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun ij kl => if ij = (kl.2, kl.1) then 1 else 0

/-- The unnormalized antisymmetric singlet vector `e_01 - e_10`. -/
def antisymmetricVector : Fin 2 × Fin 2 → ℂ :=
  fun ij => if ij = (0, 1) then 1 else if ij = (1, 0) then -1 else 0

/-- The rank-one positive matrix on the antisymmetric singlet line. -/
def singletMatrix : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.vecMulVec antisymmetricVector (star antisymmetricVector)

theorem swapMatrix_blockPositive : blockPositive swapMatrix := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  intro a b
  have hmul (x : Fin 2 × Fin 2 → ℂ) :
      Matrix.mulVec swapMatrix x = fun ij => x (ij.2, ij.1) := by
    funext ij
    obtain ⟨i, j⟩ := ij
    fin_cases i <;> fin_cases j <;>
      simp [swapMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
        Fin.sum_univ_two]
  rw [hmul]
  let z : ℂ := star (a 0) * b 0 + star (a 1) * b 1
  have hquad :
      dotProduct (star (fun ij : Fin 2 × Fin 2 => a ij.1 * b ij.2))
          (fun ij : Fin 2 × Fin 2 => a ij.2 * b ij.1) = star z * z := by
    simp [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, z, star_add, star_mul]
    ring
  rw [hquad]
  simpa [← Complex.normSq_eq_conj_mul_self] using Complex.normSq_nonneg z

theorem swapMatrix_not_posSemidef : ¬swapMatrix.PosSemidef := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  intro hswap
  have hnonneg := hswap.re_dotProduct_nonneg antisymmetricVector
  have hmul : Matrix.mulVec swapMatrix antisymmetricVector = -antisymmetricVector := by
    funext ij
    obtain ⟨i, j⟩ := ij
    fin_cases i <;> fin_cases j <;>
      simp [swapMatrix, antisymmetricVector, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [hmul] at hnonneg
  norm_num [antisymmetricVector, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_two] at hnonneg

theorem exists_blockPositive_not_posSemidef :
    ∃ W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      blockPositive W ∧ ¬W.PosSemidef := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact ⟨swapMatrix, swapMatrix_blockPositive, swapMatrix_not_posSemidef⟩

theorem singletMatrix_posSemidef : singletMatrix.PosSemidef := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact Matrix.posSemidef_vecMulVec_self_star antisymmetricVector

theorem singletMatrix_not_separable : ¬separableCone singletMatrix := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  intro hseparable
  obtain ⟨k, A, B, hAB, hsum⟩ := hseparable
  have htrace_mul_nonneg {C D : Matrix (Fin 2) (Fin 2) ℂ}
      (hC : C.PosSemidef) (hD : D.PosSemidef) :
      0 ≤ RCLike.re (Matrix.trace (C * D)) := by
    obtain ⟨r, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
    rw [Finset.sum_mul, Matrix.trace_sum]
    simp only [map_sum]
    apply Finset.sum_nonneg
    intro i hi
    have hquad := hD.re_dotProduct_nonneg (v i)
    rw [Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, dotProduct_comm,
      ← Matrix.dotProduct_mulVec]
    exact hquad
  have hswap_trace (C D : Matrix (Fin 2) (Fin 2) ℂ) :
      Matrix.trace (swapMatrix * (C ⊗ₖ D)) = Matrix.trace (C * D) := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, swapMatrix,
      Matrix.kroneckerMap, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  have hdetector_nonneg :
      0 ≤ RCLike.re (Matrix.trace (swapMatrix * singletMatrix)) := by
    rw [hsum, Finset.mul_sum, Matrix.trace_sum]
    simp only [map_sum]
    apply Finset.sum_nonneg
    intro i hi
    rw [hswap_trace]
    exact htrace_mul_nonneg (hAB i).1 (hAB i).2
  have hmul : Matrix.mulVec swapMatrix antisymmetricVector = -antisymmetricVector := by
    funext ij
    obtain ⟨i, j⟩ := ij
    fin_cases i <;> fin_cases j <;>
      simp [swapMatrix, antisymmetricVector, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [singletMatrix, Matrix.mul_vecMulVec, hmul, Matrix.trace_vecMulVec] at hdetector_nonneg
  norm_num [antisymmetricVector, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_two] at hdetector_nonneg

theorem exists_posSemidef_not_separable :
    ∃ W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      W.PosSemidef ∧ ¬separableCone W := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact ⟨singletMatrix, singletMatrix_posSemidef, singletMatrix_not_separable⟩

#print axioms swapMatrix_blockPositive
#print axioms swapMatrix_not_posSemidef
#print axioms exists_blockPositive_not_posSemidef
#print axioms singletMatrix_posSemidef
#print axioms singletMatrix_not_separable
#print axioms exists_posSemidef_not_separable

end D5.S3.Resource.CompositeConeProperness
