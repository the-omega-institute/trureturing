import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeL1
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeL1

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockBpZ
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFock
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStateField
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
open _root_.D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice
open _root_.D5.S3.VertexAlgebra.TwistedGround.NativeHyperbolicActions
open _root_.D5.S3.VertexAlgebra.TwistedGround.NativeOrbit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators TensorProduct

noncomputable section

inductive Role where
  | original
  | reflected
  deriving DecidableEq

instance : Fintype Role where
  elems := {Role.original, Role.reflected}
  complete role := by cases role <;> simp

instance : Nonempty Role := ⟨Role.original⟩

abbrev Parameters := Σ _source : Carrier data, Σ _weight : ℤ,
  Σ _exponent : ℤ, NativeTensor

abbrev signature : Signature where
  Params := Parameters
  State _ := NativeTensor
  Role := Role
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def originalReadout (parameter : Parameters) (state : NativeTensor) : ℂ :=
  let ⟨source, _weight, exponent, first⟩ := parameter
  tensorPairing ((Ytw data determinantUnit source).coeff exponent first) state

def reflectedReadout (parameter : Parameters) (state : NativeTensor) : ℂ :=
  let ⟨source, weight, exponent, first⟩ := parameter
  paritySign weight * ∑ power ∈ Finset.range
    (_root_.D5.S3.VertexAlgebra.LatticeSugawaraLocalNilpotence.oscillatorBound data source + 1),
    ((power.factorial : ℂ)⁻¹) * tensorPairing first
      ((Ytw data determinantUnit
        ((_root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents.sugawaraMode data
          explicitLeechSpectrum.inverse 1 ^ power) source)).coeff
            (-exponent - 4 * weight + 2 * (power : ℤ)) state)

def actual : Realization signature :=
  realize signature (fun role parameter state => match role with
    | .original => originalReadout parameter state
    | .reflected => reflectedReadout parameter state) (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun role _ _ => match role with
    | .original => (1 : ℂ)
    | .reflected => (0 : ℂ)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ (source : Carrier data) (weight exponent : ℤ)
    (_homogeneous : source ∈ _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy.grade data weight)
    (first second : NativeTensor),
    observation.readout Role.original ⟨source, weight, exponent, first⟩ second =
      observation.readout Role.reflected ⟨source, weight, exponent, first⟩ second

theorem exact_source_bridge :
    (type_of% (@original_native_bpz_homogeneous)) ↔ arena.Law actual := by
  exact Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact one_ne_zero (law 0 0 0 (Submodule.zero_mem _) 0 0)

private theorem actual_readout (role : Role) (parameter : Parameters) (state : NativeTensor)
    (homogeneous : parameter.1 ∈
      _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy.grade data parameter.2.1) :
    actual.readout role parameter state = originalReadout parameter state := by
  rcases parameter with ⟨source, weight, exponent, first⟩
  cases role
  · rfl
  · exact (original_native_bpz_homogeneous source weight exponent homogeneous first state).symm

private theorem source_nonzero : ∃ parameter state,
    parameter.1 ∈ _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy.grade data parameter.2.1 ∧
      originalReadout parameter state ≠ 0 := by
  let ground := nativeBasis
    (0 : _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.Half 12)
  let vacuum : NativeTensor := (1 : Oscillator data) ⊗ₜ[ℂ] ground
  have nonzero : vacuum ≠ 0 := by
    intro zero
    have coordinate := congrArg (fun state : NativeTensor => groundCoordinates state 0) zero
    have polynomialZero : (1 : Oscillator data) = 0 := by
      simpa [vacuum, ground, groundCoordinates,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply] using coordinate
    exact one_ne_zero polynomialZero
  have separation := tensor_pairing_nondegenerate explicitLeechSpectrum.inverse
    explicitLeechSpectrum.leftInverse explicitLeechSpectrum.rightInverse
  have witness : ∃ second, tensorPairing vacuum second ≠ 0 := by
    by_contra absent
    apply nonzero
    apply separation.1
    intro second
    by_contra nonzero
    exact absent ⟨second, nonzero⟩
  obtain ⟨second, nonzero⟩ := witness
  have homogeneous : (Finsupp.single 0 (1 : Oscillator data) : Carrier data) ∈
      _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy.grade data 0 := by
    rw [_root_.D5.S3.VertexAlgebra.LatticePositiveEnergy.grade_eq_span]
    apply Submodule.subset_span
    refine ⟨(0, 0), ?_, ?_⟩
    · simp [_root_.D5.S3.VertexAlgebra.LatticePositiveEnergy.energy,
        _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy.oscillatorEnergy]
    · simp [_root_.D5.S3.VertexAlgebra.LatticePositiveEnergy.carrierBasis_apply]
  refine ⟨⟨Finsupp.single 0 1, 0, 0, vacuum⟩, second, homogeneous, ?_⟩
  change tensorPairing ((Ytw data determinantUnit (Finsupp.single 0 1)).coeff 0 vacuum)
    second ≠ 0
  rw [Ytw_vacuum]
  have coefficient :
      (_root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField (V := NativeTensor)).coeff
        0 vacuum = vacuum := by
    change ((HahnModule.of ℂ).symm
      ((_root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField) vacuum)).coeff 0 = _
    rw [_root_.D5.S3.VertexAlgebra.FieldNormalProduct.identityField,
      VertexOperator.of_coeff_apply_coeff]
    rfl
  rw [coefficient]
  exact nonzero

def altered (selected : Role) : Realization signature :=
  realize signature (fun role parameter state =>
    if role = selected then (1 : ℂ) else actual.readout role parameter state)
    (fun empty => nomatch empty)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨parameter, state, homogeneous, nonzero⟩ := source_nonzero
  refine ⟨parameter, state, 0, ?_⟩
  rw [actual_readout role parameter state homogeneous, actual_readout role parameter 0 homogeneous]
  simpa [originalReadout] using nonzero

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
      have impossible := law 0 0 0 (Submodule.zero_mem _) 0 0
      cases role
      · change (1 : ℂ) = actual.readout Role.reflected ⟨0, 0, 0, 0⟩ 0
          at impossible
        rw [actual_readout _ _ _ (Submodule.zero_mem _)] at impossible
        simpa [originalReadout] using impossible
      · change actual.readout Role.original ⟨0, 0, 0, 0⟩ 0 = (1 : ℂ)
          at impossible
        rw [actual_readout _ _ _ (Submodule.zero_mem _)] at impossible
        simpa [originalReadout] using impossible
  · intro empty
    exact nomatch empty

def familyRegistration : Registration arena (type_of% (@original_native_bpz_homogeneous)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp original_native_bpz_homogeneous, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def escapeFrom := @Ytw

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_native_bpz_homogeneous)
    (type_of% (realize signature actual.readout actual.anchor)) (type_of% escapeFrom) Role where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockBpZ.original_native_bpz_homogeneous
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeL1.familyRegistration
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeL1
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms familyRegistration

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeL1
