/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/Leech
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/Leech
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal Leech native inverse matrix and original spectral basis data. -/

import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.WeightTwo
import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.DirectSum
import D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum

open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open scoped TensorProduct

noncomputable section

def LeechData : LatticeData := GolayLeech.ExplicitLeechLattice.data

set_option genInjectivity false in
structure NativeSpectrumInstance (D : LatticeData) where
  rank24 : D.rank = 24
  native : IsUnit D.G.det
  inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ
  leftInverse : inverse * gramComplex D = 1
  rightInverse : gramComplex D * inverse = 1
  coordinateEquiv : eigenspace D native inverse 2 ≃ₗ[ℂ]
    (Fin D.rank → ActualGround D native)
  basis : Module.Basis
    (Fin D.rank × LatticeTwistedGroundRealization.Half (groundRank D native)) ℂ
    (eigenspace D native inverse 2)
  basisVectors : ∀ label : Fin D.rank ×
      LatticeTwistedGroundRealization.Half (groundRank D native), (basis label).val =
    (MvPolynomial.X (label.1, 0) : Oscillator D) ⊗ₜ[ℂ]
      (Pi.single label.2 (1 : ℂ) : ActualGround D native)
  dimension : Module.finrank ℂ (eigenspace D native inverse 2) = 98304
  integralEquiv : IntegerComponents D native inverse ≃ₗ[ℂ] oddSector D native

abbrev LeechNativeSpectrum := NativeSpectrumInstance LeechData

def nativeSpectrumInstance (D : LatticeData) (native : IsUnit D.G.det)
    (inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : inverse * gramComplex D = 1)
    (rightInverse : gramComplex D * inverse = 1) (rank24 : D.rank = 24) :
    NativeSpectrumInstance D := {
  rank24 := rank24
  native := native
  inverse := inverse
  leftInverse := leftInverse
  rightInverse := rightInverse
  coordinateEquiv := weightTwoEquiv D native inverse leftInverse rightInverse rank24
  basis := weightTwoBasis D native inverse leftInverse rightInverse rank24
  basisVectors := weightTwoBasis_vector D native inverse leftInverse rightInverse rank24
  dimension := weight_two_finrank D native inverse leftInverse rightInverse rank24
  integralEquiv := integerDirectSumEquiv D native inverse leftInverse rightInverse rank24
}

def explicitLeechSpectrum : LeechNativeSpectrum := by
  let native : IsUnit LeechData.G.det := by
    change IsUnit GolayLeech.ExplicitLeechBasis.gramMatrix.det
    rw [GolayLeech.ExplicitLeechBasis.gram_determinant]
    exact isUnit_one
  have complex_determinant : (gramComplex LeechData).det = 1 := by
    rw [← Int.cast_det]
    change (GolayLeech.ExplicitLeechBasis.gramMatrix.det : ℂ) = 1
    rw [GolayLeech.ExplicitLeechBasis.gram_determinant]
    norm_num
  have complex_unit : IsUnit (gramComplex LeechData).det := by
    rw [complex_determinant]
    exact isUnit_one
  let inverse := (gramComplex LeechData)⁻¹
  have left_inverse : inverse * gramComplex LeechData = 1 :=
    Matrix.nonsing_inv_mul _ complex_unit
  have right_inverse : gramComplex LeechData * inverse = 1 :=
    Matrix.mul_nonsing_inv _ complex_unit
  exact nativeSpectrumInstance LeechData native inverse left_inverse right_inverse rfl

end
end D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
