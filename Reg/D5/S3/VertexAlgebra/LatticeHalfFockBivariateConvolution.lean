import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockBivariateConvolution

/- Exact source-type mirrors retain each original public theorem telescope; they are not registrations. -/
set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockBivariateConvolution
open _root_.D5.S3.VertexAlgebra.LatticeActualProductKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape
universe u

theorem source_actual_coefficientConvolution_monomial {Ring : Type u} [CommRing Ring]
    (creation : ℤ → Ring) (shift : ℤ) (degree : ℕ) (coefficient : Ring) : type_of% (@_root_.D5.S3.VertexAlgebra.LatticeActualProductKernel.coefficientConvolution_monomial Ring _ creation shift degree coefficient) := by
  exact @_root_.D5.S3.VertexAlgebra.LatticeActualProductKernel.coefficientConvolution_monomial Ring _ creation shift degree coefficient

theorem source_actual_coefficientConvolution_expansion {Ring : Type u} [CommRing Ring]
    (creation : ℤ → Ring) (shift : ℤ) (polynomial : Polynomial Ring) : type_of% (@_root_.D5.S3.VertexAlgebra.LatticeActualProductKernel.coefficientConvolution_expansion Ring _ creation shift polynomial) := by
  exact @_root_.D5.S3.VertexAlgebra.LatticeActualProductKernel.coefficientConvolution_expansion Ring _ creation shift polynomial

theorem source_actual_bivariateCoefficientConvolution_monomial {Ring : Type u} [CommRing Ring]
    (left right : ℤ → Ring) (first second : ℤ) (exponent : Fin 2 →₀ ℕ) (coefficient : Ring) : type_of% (@_root_.D5.S3.VertexAlgebra.LatticeActualProductKernel.bivariateCoefficientConvolution_monomial Ring _ left right first second exponent coefficient) := by
  exact @_root_.D5.S3.VertexAlgebra.LatticeActualProductKernel.bivariateCoefficientConvolution_monomial Ring _ left right first second exponent coefficient

theorem source_actual_bivariateCoefficientConvolution_C_mul {Ring : Type u} [CommRing Ring]
    (left right : ℤ → Ring) (first second : ℤ) (coefficient : Ring) (polynomial : MvPolynomial (Fin 2) Ring) : type_of% (@_root_.D5.S3.VertexAlgebra.LatticeActualProductKernel.bivariateCoefficientConvolution_C_mul Ring _ left right first second coefficient polynomial) := by
  exact @_root_.D5.S3.VertexAlgebra.LatticeActualProductKernel.bivariateCoefficientConvolution_C_mul Ring _ left right first second coefficient polynomial

theorem source_actual_bivariateCoefficientConvolution_X_zero {Ring : Type u} [CommRing Ring]
    (left right : ℤ → Ring) (first second : ℤ) (degree : ℕ) (polynomial : MvPolynomial (Fin 2) Ring) : type_of% (@_root_.D5.S3.VertexAlgebra.LatticeActualProductKernel.bivariateCoefficientConvolution_X_zero Ring _ left right first second degree polynomial) := by
  exact @_root_.D5.S3.VertexAlgebra.LatticeActualProductKernel.bivariateCoefficientConvolution_X_zero Ring _ left right first second degree polynomial

theorem source_actual_bivariateCoefficientConvolution_X_one {Ring : Type u} [CommRing Ring]
    (left right : ℤ → Ring) (first second : ℤ) (degree : ℕ) (polynomial : MvPolynomial (Fin 2) Ring) : type_of% (@_root_.D5.S3.VertexAlgebra.LatticeActualProductKernel.bivariateCoefficientConvolution_X_one Ring _ left right first second degree polynomial) := by
  exact @_root_.D5.S3.VertexAlgebra.LatticeActualProductKernel.bivariateCoefficientConvolution_X_one Ring _ left right first second degree polynomial

/- Four-slot realization, source selection and whole-family sensitivity remain open; these declarations preserve the exact source types for the audit lane. -/
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockBivariateConvolution
