/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpectralCoefficients
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpectralCoefficients
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The transfer coefficient guard and its Cartesian substitution. -/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fin.VecNotation

/-! Independent determinant coordinates and the coefficient guard of the trace-aligned mixed transfer. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpectralRadicalAlgebra

/-- The four variables of the split determinant presentation. -/
inductive Determinant
  | d | db | e | eb

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpectralRadicalAlgebra

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpecialSpectralBases

abbrev CoefficientRing (K : Type*) [CommSemiring K] := MvPolynomial (Fin 3) K

variable {K : Type*} [CommRing K]

/-- The coefficient guard used in the transfer radical chart. -/
noncomputable def guard : CoefficientRing K := MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpecialSpectralBases

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpecialDivisorExclusion

open MvPolynomial
open PeriodicMPSUniformSpecialSpectralBases (CoefficientRing guard)
open PeriodicMPSUniformSpectralRadicalAlgebra (Determinant)

noncomputable section

abbrev Variable := Option Determinant
abbrev AmbientPolynomials := MvPolynomial Variable ℂ

/-- Transfer coefficients on the independent trace-aligned variables. -/
def spectralCoefficients {R : Type*} [CommRing R] (x : Variable → R) : Fin 3 → R :=
  let d := x (some .d)
  let db := x (some .db)
  let e := x (some .e)
  let eb := x (some .eb)
  let k := x none
  let U := d * db
  let b := U - e * eb
  ![d + db - 2 * (U + e * eb) - k ^ 2, b, b ^ 2 + k ^ 2 * (d + eb) * (db + e)]

def coefficientSubstitution : CoefficientRing ℂ →+* AmbientPolynomials :=
  eval₂Hom C (spectralCoefficients X)

def ambientU : AmbientPolynomials := X (some .d) * X (some .db)
def ambientK : AmbientPolynomials := X none

def ambientGuard : AmbientPolynomials := ambientU * ambientK * coefficientSubstitution guard

theorem ambientGuard_formula :
    ambientGuard = ambientU * ambientK *
      (spectralCoefficients (X : Variable → AmbientPolynomials) 2 -
        spectralCoefficients (X : Variable → AmbientPolynomials) 1 ^ 2) := by
  simp only [ambientGuard, PeriodicMPSUniformSpecialSpectralBases.guard, map_sub, map_pow,
    coefficientSubstitution, eval₂Hom_X']

private def nativeCartesian (x : Variable → AmbientPolynomials) : Fin 5 → AmbientPolynomials :=
  ![C (1 / 2) * (x (some .d) + x (some .db)),
    x none,
    C (1 / 2) * (x (some .e) + x (some .eb)),
    C ((2 * Complex.I)⁻¹) * (x (some .d) - x (some .db)),
    C ((2 * Complex.I)⁻¹) * (x (some .e) - x (some .eb))]

/-- The native Cartesian order is Re d, k, Re e, Im d, Im e.
The ambient coordinates d, db, e and eb are independent over ℂ. -/
def nativeSliceSubstitution : MvPolynomial (Fin 5) ℂ →+* AmbientPolynomials :=
  eval₂Hom C (nativeCartesian X)

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpecialDivisorExclusion
