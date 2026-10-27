import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor.LocalResidues
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Exact source predicates and positive laws for the signed local residues.
These equivalences retain every argument of the mathematical statements.
They establish neither whole-family variation nor observational dependence. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor.LocalResidues
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor.LocalResidues
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockOuterTaylorEvaluation UniformGradedLocalCorrelator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open SupportedFieldWords.FiniteConvolution
open CollisionRationalExpansions.OrderedRationalExpansion
open CollisionRationalExpansions.HahnFiberResidue
open CollisionRationalExpansions.HahnFiberScalar
open CollisionRationalExpansions.FullOrderSpectatorPole
open CollisionLaurentKernels.LaurentCollision
open CollisionLaurentKernels.RationalFusedResidue
open OrderedCollisionCoordinates.ContextualLaurentKernel
open OrderedCollisionCoordinates.AdjacentFullOrders
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open LabelledRationalClearing.GlobalRationalCurry
open OrderedCollisionCoordinates.LocalResidueCurrying
open scoped BigOperators VertexOperator RatFunc
noncomputable section

def source_second_source_coefficients (M j : ℕ) (R : CommonRational ℂ 3)
    (k l : ℤ) : Prop :=
    lastSourceLocalQ 0 true 1 j M k l R =
      (coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder
        (secondSourceRational M j R)).coeff (exponents 2 ![-l - 1, -k - 1]) ∧
    lastSourceLocalQ 0 false 1 j M k l R =
      (coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder
        (secondSourceRational M j R)).coeff (exponents 2 ![-k - 1, -l - 1])

theorem second_source_coefficients_source_iff (M j : ℕ) (R : CommonRational ℂ 3)
    (k l : ℤ) :
    source_second_source_coefficients M j R k l ↔
    (lastSourceLocalQ 0 true 1 j M k l R =
      (coefficientHahn ℂ 2 0 (0 : Fin 3) secondSourceLeftOrder
        (secondSourceRational M j R)).coeff (exponents 2 ![-l - 1, -k - 1]) ∧
    lastSourceLocalQ 0 false 1 j M k l R =
      (coefficientHahn ℂ 1 1 (0 : Fin 3) secondSourceRightOrder
        (secondSourceRational M j R)).coeff (exponents 2 ![-k - 1, -l - 1])) := Iff.rfl

theorem second_source_coefficients_actual (M j : ℕ) (R : CommonRational ℂ 3)
    (k l : ℤ) :
    source_second_source_coefficients M j R k l := by
  exact _root_.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor.LocalResidues.second_source_coefficients M j R k l

def source_second_source_rational_evaluation (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (j : ℕ) : Prop :=
    secondSourceRational (vectorFrequencyBound D b + 1) j
      (algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) =
      secondSourceTaylorRational D a b K P j

theorem second_source_rational_evaluation_source_iff (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (j : ℕ) :
    source_second_source_rational_evaluation D a b K P j ↔
    (secondSourceRational (vectorFrequencyBound D b + 1) j
      (algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) =
      secondSourceTaylorRational D a b K P j) := Iff.rfl

theorem second_source_rational_evaluation_actual (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (j : ℕ) :
    source_second_source_rational_evaluation D a b K P j := by
  exact _root_.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor.LocalResidues.second_source_rational_evaluation D a b K P j

def source_rational_joint_support (T : SecondSourceField) (r n : ℤ) (H : ℕ) : Prop :=
    (∀ ell ∈ Finset.range ((H : ℤ) - (r)).toNat,
      Function.HasFiniteSupport (fun u : ℕ =>
        BinomialKernelDelta.chooseSign ((r) + ell) u *
          secondSourceForward T ((r) + ell - u) ((n) - ell + u)) ∧
      Function.HasFiniteSupport (fun u : ℕ =>
        BinomialKernelDelta.chooseSign ((r) + ell) u *
          secondSourceBackward T ((r) + (n) - u) u)) ∧
    Function.HasFiniteSupport (secondSourceJointTerm false T r n H) ∧
    Function.HasFiniteSupport (secondSourceJointTerm true T r n H)

theorem rational_joint_support_source_iff (T : SecondSourceField) (r n : ℤ) (H : ℕ) :
    source_rational_joint_support T r n H ↔
    ((∀ ell ∈ Finset.range ((H : ℤ) - (r)).toNat,
      Function.HasFiniteSupport (fun u : ℕ =>
        BinomialKernelDelta.chooseSign ((r) + ell) u *
          secondSourceForward T ((r) + ell - u) ((n) - ell + u)) ∧
      Function.HasFiniteSupport (fun u : ℕ =>
        BinomialKernelDelta.chooseSign ((r) + ell) u *
          secondSourceBackward T ((r) + (n) - u) u)) ∧
    Function.HasFiniteSupport (secondSourceJointTerm false T r n H) ∧
    Function.HasFiniteSupport (secondSourceJointTerm true T r n H)) := Iff.rfl

theorem rational_joint_support_actual (T : SecondSourceField) (r n : ℤ) (H : ℕ) :
    source_rational_joint_support T r n H := by
  exact _root_.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor.LocalResidues.rational_joint_support T r n H

def source_source_monomial_complete_residue
    (p q t r n : ℤ) (c : ℂ) : Prop :=
    completeOuterResidue r n
      (secondSourceForward (sourceMonomial p q c * (vVar - zVar) ^ t))
      (secondSourceBackward (sourceMonomial p q c * (vVar - zVar) ^ t)) 0 =
      if r + t < 0 then
        if p + q = -(r + t) - n - 2 then
          c * ((Ring.choose p (-(r + t) - 1).toNat : ℤ) : ℂ) else 0
      else 0

theorem source_monomial_complete_residue_source_iff
    (p q t r n : ℤ) (c : ℂ) :
    source_source_monomial_complete_residue p q t r n c ↔
    (completeOuterResidue r n
      (secondSourceForward (sourceMonomial p q c * (vVar - zVar) ^ t))
      (secondSourceBackward (sourceMonomial p q c * (vVar - zVar) ^ t)) 0 =
      if r + t < 0 then
        if p + q = -(r + t) - n - 2 then
          c * ((Ring.choose p (-(r + t) - 1).toNat : ℤ) : ℂ) else 0
      else 0) := Iff.rfl

theorem source_monomial_complete_residue_actual
    (p q t r n : ℤ) (c : ℂ) :
    source_source_monomial_complete_residue p q t r n c := by
  exact _root_.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor.LocalResidues.source_monomial_complete_residue p q t r n c

def source_source_inner_monomial_normal_form
    (D : LatticeData) (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3)
    (j alpha : ℕ) (e : Exponent 3) : Prop :=
    secondSourceInnerTaylorTerm D a b K P j alpha e =
      ∑ h ∈ Finset.range (vectorFrequencyBound D b + 1 - j - alpha),
        let k := vectorFrequencyBound D b + 1 - j - alpha - 1 - h
        sourceMonomial (e 1) (e 0 + e 2 - alpha - h)
          (Ring.choose (-(1 : ℂ) / 2) alpha * P.coeff e *
            ((Ring.choose (e 0) h : ℤ) : ℂ) *
            ((Ring.choose (-(vectorFrequencyBound D a + 1 : ℤ)) k : ℤ) : ℂ) *
            StateFieldResidueReconstruction.epsilon
              (-(vectorFrequencyBound D a + 1 : ℤ) - k)) *
          (vVar - zVar) ^
            (-(K : ℤ) - (vectorFrequencyBound D a + 1 : ℤ) - k)

theorem source_inner_monomial_normal_form_source_iff
    (D : LatticeData) (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3)
    (j alpha : ℕ) (e : Exponent 3) :
    source_source_inner_monomial_normal_form D a b K P j alpha e ↔
    (secondSourceInnerTaylorTerm D a b K P j alpha e =
      ∑ h ∈ Finset.range (vectorFrequencyBound D b + 1 - j - alpha),
        let k := vectorFrequencyBound D b + 1 - j - alpha - 1 - h
        sourceMonomial (e 1) (e 0 + e 2 - alpha - h)
          (Ring.choose (-(1 : ℂ) / 2) alpha * P.coeff e *
            ((Ring.choose (e 0) h : ℤ) : ℂ) *
            ((Ring.choose (-(vectorFrequencyBound D a + 1 : ℤ)) k : ℤ) : ℂ) *
            StateFieldResidueReconstruction.epsilon
              (-(vectorFrequencyBound D a + 1 : ℤ) - k)) *
          (vVar - zVar) ^
            (-(K : ℤ) - (vectorFrequencyBound D a + 1 : ℤ) - k)) := Iff.rfl

theorem source_inner_monomial_normal_form_actual
    (D : LatticeData) (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3)
    (j alpha : ℕ) (e : Exponent 3) :
    source_source_inner_monomial_normal_form D a b K P j alpha e := by
  exact _root_.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor.LocalResidues.source_inner_monomial_normal_form D a b K P j alpha e

def source_second_source_monomial_taylor_index
    (D : LatticeData) (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3)
    (j alpha : ℕ) (e : Exponent 3) (hα : alpha < vectorFrequencyBound D b + 1 - j) : Prop :=
    secondSourceTerm D a b K P j alpha e =
      secondSourceInnerTaylorTerm D a b K P j alpha e

theorem second_source_monomial_taylor_index_source_iff
    (D : LatticeData) (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3)
    (j alpha : ℕ) (e : Exponent 3) (hα : alpha < vectorFrequencyBound D b + 1 - j) :
    source_second_source_monomial_taylor_index D a b K P j alpha e hα ↔
    (secondSourceTerm D a b K P j alpha e =
      secondSourceInnerTaylorTerm D a b K P j alpha e) := Iff.rfl

theorem second_source_monomial_taylor_index_actual
    (D : LatticeData) (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3)
    (j alpha : ℕ) (e : Exponent 3) (hα : alpha < vectorFrequencyBound D b + 1 - j) :
    source_second_source_monomial_taylor_index D a b K P j alpha e hα := by
  exact _root_.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor.LocalResidues.second_source_monomial_taylor_index D a b K P j alpha e hα

end
end Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor.LocalResidues
