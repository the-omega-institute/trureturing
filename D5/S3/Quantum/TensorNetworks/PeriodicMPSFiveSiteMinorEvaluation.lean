/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorEvaluation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorEvaluation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Exact residue-field evaluation of the first five-site critical minor. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteLineMinors
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorFactorization

/-! A triangular factorization certifies a point evaluation of the residual minor. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorEvaluation

open Matrix PeriodicMPSFiveSiteLineMinors PeriodicMPSFiveSiteMinorFactorization

private abbrev F := ZMod 1009

/-- A triangular factorization without a row permutation certifies a selected
residue-field determinant by its diagonal product. -/
theorem value_of_factors {x : F} {k : Fin 10} {v : F}
    (L U : Matrix (Fin 9) (Fin 9) F)
    (hLU : ∀ i j, (jacobian (line x)).submatrix k.succAbove k.succAbove i j = (L * U) i j)
    (hL : L.IsLowerTriangular) (hLdiag : ∀ i, L i i = 1)
    (hU : U.IsUpperTriangular) (hv : ∏ i, U i i = v) :
    residualMinor x k = v := by
  let A := (jacobian (line x)).submatrix k.succAbove k.succAbove
  have h : A.submatrix (1 : Equiv.Perm (Fin 9)) id = L * U := by
    ext i j
    exact hLU i j
  change A.det = v
  simpa using (determinant_of_factors A L U 1 h hL hLdiag hU).trans (by simpa using hv)

private def L : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    864, 1, 0, 0, 0, 0, 0, 0, 0;
    938, 611, 1, 0, 0, 0, 0, 0, 0;
    959, 50, 351, 1, 0, 0, 0, 0, 0;
    649, 466, 503, 958, 1, 0, 0, 0, 0;
    847, 159, 67, 28, 85, 1, 0, 0, 0;
    274, 296, 702, 208, 502, 443, 1, 0, 0;
    143, 502, 555, 820, 1008, 408, 816, 1, 0;
    549, 887, 314, 19, 355, 803, 242, 916, 1]

private def U : Matrix (Fin 9) (Fin 9) F :=
  !![683, 29, 955, 419, 36, 709, 978, 494, 695;
    0, 242, 604, 145, 319, 137, 595, 286, 878;
    0, 0, 426, 297, 189, 502, 790, 745, 688;
    0, 0, 0, 272, 322, 348, 880, 765, 979;
    0, 0, 0, 0, 466, 975, 994, 968, 223;
    0, 0, 0, 0, 0, 566, 666, 809, 71;
    0, 0, 0, 0, 0, 0, 743, 430, 950;
    0, 0, 0, 0, 0, 0, 0, 164, 652;
    0, 0, 0, 0, 0, 0, 0, 0, 287]

private def rowPermutation : Equiv.Perm (Fin 9) := 1

private def A : Matrix (Fin 9) (Fin 9) F :=
  (jacobian (line (0 : F))).submatrix (0 : Fin 10).succAbove (0 : Fin 10).succAbove

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- Check the 81 matrix entries separately.
private theorem factorization : A.submatrix rowPermutation id = L * U := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem lower : L.IsLowerTriangular := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel

private theorem upper : U.IsUpperTriangular := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel

private theorem unit_diag (i : Fin 9) : L i i = 1 := by
  fin_cases i <;> decide +kernel

/-- The first residue-field evaluation of the first selected minor. -/
theorem first_at_zero : residualMinor (0 : F) 0 = 758 := by
  change A.det = _
  rw [determinant_of_factors A L U rowPermutation factorization lower unit_diag upper]
  simp [rowPermutation, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap', U, Fin.prod_univ_succ]
  decide +kernel

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorEvaluation
