/- GID: D5/S3/PrimeForms/Symmetry/FixedFormInversion
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Symmetry/FixedFormInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The fixed-point form of an SL(2,Z) matrix changes sign under inversion. -/

import D5.S3.PrimeForms.EisensteinDiscriminant
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

namespace D5.S3.PrimeForms.Symmetry.FixedFormInversion

open D5.S3.PrimeForms.EisensteinDiscriminant

/-- The fixed-point binary quadratic form `c*x^2 + (d-a)*x - b` associated to
the matrix `[[a, b], [c, d]]`. -/
def fixedForm (gamma : Matrix.SpecialLinearGroup (Fin 2) Int) : BinaryQuadraticForm where
  a := gamma 1 0
  b := gamma 1 1 - gamma 0 0
  c := -gamma 0 1

/-- Coefficientwise negation of a binary quadratic form. -/
def negateForm (f : BinaryQuadraticForm) : BinaryQuadraticForm where
  a := -f.a
  b := -f.b
  c := -f.c

/-- Inverting an integral determinant-one matrix negates its fixed-point quadratic form. -/
theorem fixed_form_inverse_eq_neg (gamma : Matrix.SpecialLinearGroup (Fin 2) Int) :
    fixedForm gamma⁻¹ = negateForm (fixedForm gamma) := by
  ext <;> simp [fixedForm, negateForm, Matrix.SpecialLinearGroup.SL2_inv_expl]

#print axioms fixed_form_inverse_eq_neg

end D5.S3.PrimeForms.Symmetry.FixedFormInversion
