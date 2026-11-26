/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorEvaluation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorEvaluation
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Exact residue-field evaluation of the six-site critical minor. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteLineMinors
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteLineBezout
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorFactorization

/-! A triangular factorization certifies a point evaluation of the residual minor. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorEvaluation

open Matrix PeriodicMPSSixSiteLineMinors PeriodicMPSFiveSiteMinorFactorization
open PeriodicMPSFiveSiteLineMinors (line)

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

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorEvaluation
