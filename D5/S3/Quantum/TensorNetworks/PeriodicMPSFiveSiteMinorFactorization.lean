/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorFactorization
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorFactorization
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Check a determinant via a unit lower and an upper triangular factor. -/
import Mathlib.LinearAlgebra.Matrix.Block

/-! A finite factorization certificate avoids expanding the determinant by permutations. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorFactorization

open Matrix

/-- A row permutation and unit-lower triangular factor reduce a determinant to
the product of the upper triangular factor's diagonal. -/
theorem determinant_of_factors {R : Type*} [CommRing R] {n : ℕ}
    (A L U : Matrix (Fin n) (Fin n) R) (p : Equiv.Perm (Fin n))
    (hLU : A.submatrix p id = L * U)
    (hL : L.IsLowerTriangular) (hLdiag : ∀ i, L i i = 1)
    (hU : U.IsUpperTriangular) :
    A.det = (Equiv.Perm.sign p : R) * ∏ i, U i i := by
  have hs : (Equiv.Perm.sign p : R) * (Equiv.Perm.sign p : R) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simp [h]
  have h := congrArg Matrix.det hLU
  rw [Matrix.det_permute, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ hL,
    Matrix.det_of_isUpperTriangular hU] at h
  simp only [hLdiag, Finset.prod_const_one, one_mul] at h
  calc
    A.det = ((Equiv.Perm.sign p : R) * (Equiv.Perm.sign p : R)) * A.det := by rw [hs, one_mul]
    _ = (Equiv.Perm.sign p : R) * ∏ i, U i i := by rw [mul_assoc, h]

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorFactorization
