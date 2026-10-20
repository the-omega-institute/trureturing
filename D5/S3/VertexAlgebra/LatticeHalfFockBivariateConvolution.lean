/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Completed generic bivariate convolution suppliers for native physical products. -/


import D5.S3.VertexAlgebra.LatticeActualProductKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeActualProductKernel

noncomputable section
def coefficientConvolution {Ring : Type*} [CommRing Ring]
    (creation : ℤ → Ring) (shift : ℤ) : Polynomial Ring →ₗ[Ring] Ring :=
  (Finsupp.lsum Ring (fun degree : ℕ =>
    LinearMap.mulRight Ring (creation (shift + degree)))).comp
      ((AddMonoidAlgebra.coeffLinearEquiv Ring).toLinearMap.comp
        (Polynomial.toFinsuppIsoLinear Ring).toLinearMap)

theorem coefficientConvolution_monomial {Ring : Type*} [CommRing Ring]
    (creation : ℤ → Ring) (shift : ℤ) (degree : ℕ) (coefficient : Ring) :
    coefficientConvolution creation shift (Polynomial.monomial degree coefficient) =
      coefficient * creation (shift + degree) := by
  simp [coefficientConvolution, Polynomial.toFinsupp_monomial]

theorem coefficientConvolution_expansion {Ring : Type*} [CommRing Ring]
    (creation : ℤ → Ring) (shift : ℤ) (polynomial : Polynomial Ring) :
    coefficientConvolution creation shift polynomial =
      ∑ degree ∈ polynomial.support, polynomial.coeff degree * creation (shift + degree) := by
  classical
  first
  | rfl
  | calc
      coefficientConvolution creation shift polynomial =
          coefficientConvolution creation shift
            (polynomial.sum fun degree coefficient => Polynomial.monomial degree coefficient) :=
        congrArg (coefficientConvolution creation shift) (Polynomial.sum_monomial_eq polynomial).symm
      _ = _ := by
        change coefficientConvolution creation shift
          (∑ degree ∈ polynomial.support, Polynomial.monomial degree (polynomial.coeff degree)) = _
        simp only [map_sum, coefficientConvolution_monomial]

def bivariateCoefficientConvolution {Ring : Type*} [CommRing Ring]
    (left right : ℤ → Ring) (first second : ℤ) :
    MvPolynomial (Fin 2) Ring →ₗ[Ring] Ring :=
  (Finsupp.lsum Ring (fun exponent : Fin 2 →₀ ℕ =>
    LinearMap.mulRight Ring (left (first + exponent 0) * right (second + exponent 1)))).comp
      (AddMonoidAlgebra.coeffLinearEquiv Ring).toLinearMap

theorem bivariateCoefficientConvolution_monomial {Ring : Type*} [CommRing Ring]
    (left right : ℤ → Ring) (first second : ℤ) (exponent : Fin 2 →₀ ℕ) (coefficient : Ring) :
    bivariateCoefficientConvolution left right first second (MvPolynomial.monomial exponent coefficient) =
      coefficient * (left (first + exponent 0) * right (second + exponent 1)) := by
  simp [bivariateCoefficientConvolution, MvPolynomial.monomial, mul_assoc]

theorem bivariateCoefficientConvolution_C_mul {Ring : Type*} [CommRing Ring]
    (left right : ℤ → Ring) (first second : ℤ) (coefficient : Ring)
    (polynomial : MvPolynomial (Fin 2) Ring) :
    bivariateCoefficientConvolution left right first second (MvPolynomial.C coefficient * polynomial) =
      coefficient * bivariateCoefficientConvolution left right first second polynomial := by
  rw [MvPolynomial.C_mul']
  exact map_smul _ _ _

theorem bivariateCoefficientConvolution_X_zero {Ring : Type*} [CommRing Ring]
    (left right : ℤ → Ring) (first second : ℤ) (degree : ℕ)
    (polynomial : MvPolynomial (Fin 2) Ring) :
    bivariateCoefficientConvolution left right first second (MvPolynomial.X 0 ^ degree * polynomial) =
      bivariateCoefficientConvolution left right (first + degree) second polynomial := by
  classical
  induction polynomial using MvPolynomial.induction_on' with
  | add firstPolynomial secondPolynomial firstProof secondProof =>
    simp only [mul_add, map_add, firstProof, secondProof]
  | monomial exponent coefficient =>
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
      bivariateCoefficientConvolution_monomial, bivariateCoefficientConvolution_monomial]
    simp only [one_mul, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), zero_add]
    congr 3
    push_cast
    omega

theorem bivariateCoefficientConvolution_X_one {Ring : Type*} [CommRing Ring]
    (left right : ℤ → Ring) (first second : ℤ) (degree : ℕ)
    (polynomial : MvPolynomial (Fin 2) Ring) :
    bivariateCoefficientConvolution left right first second (MvPolynomial.X 1 ^ degree * polynomial) =
      bivariateCoefficientConvolution left right first (second + degree) polynomial := by
  classical
  induction polynomial using MvPolynomial.induction_on' with
  | add firstPolynomial secondPolynomial firstProof secondProof =>
    simp only [mul_add, map_add, firstProof, secondProof]
  | monomial exponent coefficient =>
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
      bivariateCoefficientConvolution_monomial, bivariateCoefficientConvolution_monomial]
    simp only [one_mul, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), zero_add]
    congr 3
    push_cast
    omega

end
end D5.S3.VertexAlgebra.LatticeActualProductKernel
