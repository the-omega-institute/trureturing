/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueDeterminant
   generality: I
   mirror-B: none(waiver:ordinary-seven-site-certificate-supplier)
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorFactorization]
   utility: none
   digest: Evaluation of residue polynomials and the triangular determinant specialization used by the cofactor batches. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueData
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorFactorization

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

open Matrix Polynomial
open PeriodicMPSFiveSiteMinorFactorization (determinant_of_factors)

def coefficientValue {n : ℕ} (a : Fin n → F) (u : F) : F :=
  ∑ j : Fin n, a j * u ^ (j : ℕ)

theorem eval_ofFn {n : ℕ} (a : Fin n → F) (u : F) :
    (ofFn n a).eval u = coefficientValue a u := by
  simp [coefficientValue, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]

def valueAt (u : F) (ab : Fin 4 × Fin 4) : F :=
  coefficientValue (valueCoefficients ab.1 ab.2) u

def partialAt (u : F) (r : Fin 10) (j : Fin 5) : F :=
  coefficientValue (partialCoefficients r j) u

def evaluatedRows (u : F) (deleted : Fin 10) : Matrix (Fin 9) (Fin 9) F :=
  fun i j =>
    let r := deleted.succAbove i
    let ab := observedRow r
    if h : j.val < 5 then partialAt u r ⟨j.val, h⟩
    else if j = 5 then valueAt u ab
    else
      let a := rotationIndex ⟨j.val - 6, by omega⟩ ab.1
      let b := rotationIndex ⟨j.val - 6, by omega⟩ ab.2
      (a.1 : F) * valueAt u (a.2, ab.2) + (b.1 : F) * valueAt u (ab.1, b.2)

def quotientCoefficients (r : Fin 10) : Fin 47 → F :=
  if r = 0 then quotient_0 else quotient_1

def quotientValue (r : Fin 10) (u : F) : F :=
  coefficientValue (quotientCoefficients r) u

noncomputable def lineQuotient (r : Fin 10) : F[X] :=
  ofFn 47 (quotientCoefficients r)

theorem eval_lineQuotient (r : Fin 10) (u : F) :
    (lineQuotient r).eval u = quotientValue r u := eval_ofFn _ _

theorem det_of_factors {A : Matrix (Fin 9) (Fin 9) F} {v : F}
    (L U : Matrix (Fin 9) (Fin 9) F) (hLU : ∀ i j, A i j = (L * U) i j)
    (hL : L.IsLowerTriangular) (hLdiag : ∀ i, L i i = 1)
    (hU : U.IsUpperTriangular) (hv : ∏ i, U i i = v) :
    A.det = v := by
  have h : A.submatrix (1 : Equiv.Perm (Fin 9)) id = L * U := by
    ext i j
    exact hLU i j
  simpa [hv] using determinant_of_factors A L U 1 h hL hLdiag hU

end D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate
