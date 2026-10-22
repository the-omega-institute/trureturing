import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Charged
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency true

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Charged

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockBpZ
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice
open _root_.D5.S3.VertexAlgebra.TwistedGround.NativeHyperbolicActions
open _root_.D5.S3.VertexAlgebra.TwistedGround.NativeOrbit
open _root_.D5.S3.VertexAlgebra.TwistedGround.NativeSymmetricForm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators TensorProduct

noncomputable section

inductive Role where
  | charged
  | reflected
  deriving DecidableEq

instance : Fintype Role where
  elems := {Role.charged, Role.reflected}
  complete role := by cases role <;> simp

instance : Nonempty Role := ⟨Role.charged⟩

abbrev Parameters := Charge data × ℤ × NativeTensor

abbrev signature : Signature where
  Params := Parameters
  State _ := NativeTensor
  Role := Role
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role parameter state => match role with
    | .charged => tensorPairing
        (chargedCoefficient data determinantUnit parameter.1 parameter.2.1 state) parameter.2.2
    | .reflected => chargeScalar data parameter.1 * tensorPairing state
        (TensorProduct.map
          (oscillatorCoefficient data parameter.1
            (-2 * chargeNorm data parameter.1 - parameter.2.1))
          (epsilon data parameter.1 (-parameter.1) •
            groundAction data determinantUnit (-parameter.1)) parameter.2.2))
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun role _ _ => match role with
    | .charged => (1 : ℂ)
    | .reflected => (0 : ℂ)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter state,
    observation.readout Role.charged parameter state =
      observation.readout Role.reflected parameter state

theorem exact_source_bridge :
    (type_of% (@tensor_charged_adjoint)) ↔ arena.Law actual := by
  constructor
  · intro source parameter state
    exact source parameter.1 parameter.2.1 state parameter.2.2
  · intro law charge exponent first second
    exact law ⟨charge, exponent, second⟩ first

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := law ⟨0, 0, 0⟩ (0 : NativeTensor)
  exact one_ne_zero impossible

private theorem actual_readout (role : Role) (parameter : Parameters) (state : NativeTensor) :
    actual.readout role parameter state = tensorPairing
      (chargedCoefficient data determinantUnit parameter.1 parameter.2.1 state) parameter.2.2 := by
  cases role
  · rfl
  · exact (tensor_charged_adjoint parameter.1 parameter.2.1 state parameter.2.2).symm

private theorem vacuum_coefficient : oscillatorCoefficient data 0 0 1 = 1 := by
  have normZero : chargeNorm data 0 = 0 := by simp [chargeNorm, bilinear]
  change (∑ᶠ degree : ℕ, oscillatorTerm data 0 0 1 degree) = 1
  rw [finsum_eq_sum_of_support_subset _ (term_support data 0 0 1)]
  rw [show halfTranslatedPolynomial data 0 1 = (1 : Polynomial (Oscillator data)) by
    exact map_one (MvPolynomial.eval₂AlgHom ℂ (halfTranslationVariable data 0))]
  rw [show (1 : Polynomial (Oscillator data)).support = {0} by
    simpa using Polynomial.support_X_pow (R := Oscillator data) 0]
  simp [oscillatorTerm, halfTranslatedPolynomial, normZero,
    halfCreationCoeff, exponential_constant]

private theorem ground_zero : groundAction data determinantUnit 0 =
    (1 : Module.End ℂ NativeGround) := by
  change groundRepresentation data determinantUnit 1 = 1
  exact map_one _

private theorem charged_vacuum (ground : NativeGround) :
    chargedCoefficient data determinantUnit 0 0 ((1 : Oscillator data) ⊗ₜ[ℂ] ground) =
      ((1 : Oscillator data) ⊗ₜ[ℂ] ground) := by
  have normZero : chargeNorm data 0 = 0 := by simp [chargeNorm, bilinear]
  simp [chargedCoefficient, chargeScalar, normZero, vacuum_coefficient, ground_zero]

private theorem vacuum_pairing :
    tensorPairing ((1 : Oscillator data) ⊗ₜ[ℂ] nativeBasis 0)
      ((1 : Oscillator data) ⊗ₜ[ℂ] nativeBasis 0) = 1 := by
  have oscillator : oscillatorPairing data 1 1 = 1 := by
    have constantRight : ∀ polynomial : Oscillator data, ∀ scalar : ℂ,
        oscillatorPairing data polynomial (MvPolynomial.C scalar) =
          scalar * MvPolynomial.constantCoeff polynomial := by
      run_tac
        let supplier := (Lean.Name.num
          `_private.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Transpose 0).append
          `D5.S3.VertexAlgebra.LatticeHalfFockBpZ.oscillator_constant_right
        Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent supplier) _))
    simpa using constantRight 1 1
  rw [tensor_pairing_tmul, oscillator, basis_pairing, if_pos rfl, mul_one]

def altered (selected : Role) : Realization signature :=
  realize signature (fun role parameter state =>
    if role = selected then (1 : ℂ) else actual.readout role parameter state)
    (fun empty => nomatch empty)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  change Role at role
  let vacuum : NativeTensor := (1 : Oscillator data) ⊗ₜ[ℂ] nativeBasis 0
  refine ⟨⟨0, 0, vacuum⟩, vacuum, 0, ?_⟩
  rw [actual_readout, actual_readout]
  change ¬ tensorPairing (chargedCoefficient data determinantUnit 0 0 vacuum) vacuum =
    tensorPairing (chargedCoefficient data determinantUnit 0 0 0) vacuum
  rw [map_zero, map_zero]
  dsimp only [vacuum]
  rw [charged_vacuum, vacuum_pairing]
  exact one_ne_zero

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro role
    change Role at role
    refine ⟨altered role, ?_, rfl, ?_⟩
    · intro other different
      change Role at other
      funext parameter state
      change actual.readout other parameter state =
        (if other = role then (1 : ℂ) else actual.readout other parameter state)
      exact (if_neg different).symm
    · intro law
      have impossible := law ⟨0, 0, 0⟩ (0 : NativeTensor)
      cases role
      · change (1 : ℂ) = actual.readout Role.reflected ⟨0, 0, 0⟩ 0 at impossible
        rw [actual_readout] at impossible
        simp only [map_zero] at impossible
        exact one_ne_zero impossible
      · change actual.readout Role.charged ⟨0, 0, 0⟩ 0 = (1 : ℂ) at impossible
        rw [actual_readout] at impossible
        simp only [map_zero] at impossible
        exact zero_ne_one impossible
  · intro empty
    exact nomatch empty

def familyRegistration : Registration arena (type_of% (@tensor_charged_adjoint)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp tensor_charged_adjoint, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def escapeFrom := @chargedCoefficient

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tensor_charged_adjoint)
    (type_of% (realize signature actual.readout actual.anchor)) (type_of% escapeFrom) Role where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockBpZ.tensor_charged_adjoint
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Charged.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨familyRegistration.variation⟩ trivial
  sensitivity := .evidence ⟨familyRegistration.sensitivity⟩ trivial
  partialSensitivity := none
  escapeFrom := some escapeFrom
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Charged
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := some ⟨arena, ⟨familyRegistration⟩⟩
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms familyRegistration

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Charged
