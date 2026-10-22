import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeReflection
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeReflection

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

abbrev Parameters := Σ _charge : Charge data, Σ _axis : Fin data.rank,
  Σ _order : ℕ, Σ _exponent : ℤ, NativeTensor

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
  let ⟨charge, axis, order, exponent, first⟩ := parameter
  tensorPairing ((Ytw data determinantUnit
    (Finsupp.single charge (MvPolynomial.X (axis, order)))).coeff exponent first) state

def reflectedReadout (parameter : Parameters) (state : NativeTensor) : ℂ :=
  let ⟨charge, axis, order, exponent, first⟩ := parameter
  (∑ reduced ∈ Finset.range (order + 1),
    jetReflectionScalar order reduced * tensorPairing first
      ((nativeOppositeYtw
        (Finsupp.single charge (MvPolynomial.X (axis, reduced)))).coeff
          (-2 * chargeNorm data charge - exponent - 2 * order - 2 * reduced - 4) state)) +
    ((-1 : ℂ) ^ (order + 1) *
      (bilinear data (unitCharge data axis) charge : ℂ)) *
      tensorPairing first ((nativeOppositeYtw (Finsupp.single charge 1)).coeff
        (-2 * chargeNorm data charge - exponent - 2 * order - 2) state)

def actual : Realization signature :=
  realize signature (fun role parameter state => match role with
    | .original => originalReadout parameter state
    | .reflected => reflectedReadout parameter state)
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun role _ _ => match role with
    | .original => (1 : ℂ)
    | .reflected => (0 : ℂ)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ (charge : Charge data) (axis : Fin data.rank)
    (order : ℕ) (exponent : ℤ) (first second : NativeTensor),
    observation.readout Role.original ⟨charge, axis, order, exponent, first⟩ second =
      observation.readout Role.reflected ⟨charge, axis, order, exponent, first⟩ second

theorem exact_source_bridge :
    (type_of% (@original_jet_source_reflection)) ↔ arena.Law actual := by
  exact Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact one_ne_zero (law 0 0 0 0 0 0)

private theorem actual_readout (role : Role) (parameter : Parameters) (state : NativeTensor) :
    actual.readout role parameter state = originalReadout parameter state := by
  rcases parameter with ⟨charge, axis, order, exponent, first⟩
  cases role
  · rfl
  · exact (original_jet_source_reflection charge axis order exponent first state).symm

private theorem source_nonzero : ∃ parameter state, originalReadout parameter state ≠ 0 := by
  let ground := nativeBasis (0 : _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.Half 12)
  let created : NativeTensor := (MvPolynomial.X (0, 0) : Oscillator data) ⊗ₜ[ℂ] ground
  have createdNonzero : created ≠ 0 := by
    intro zero
    have coordinate := congrArg (fun state : NativeTensor => groundCoordinates state 0) zero
    have polynomialZero : (MvPolynomial.X (0, 0) : Oscillator data) = 0 := by
      simpa [created, ground, groundCoordinates,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply] using coordinate
    exact MvPolynomial.X_ne_zero (0, 0) polynomialZero
  have separation := tensor_pairing_nondegenerate explicitLeechSpectrum.inverse
    explicitLeechSpectrum.leftInverse explicitLeechSpectrum.rightInverse
  have witness : ∃ second, tensorPairing created second ≠ 0 := by
    by_contra absent
    apply createdNonzero
    apply separation.1
    intro second
    by_contra nonzero
    exact absent ⟨second, nonzero⟩
  obtain ⟨second, nonzero⟩ := witness
  let vacuum : NativeTensor := (1 : Oscillator data) ⊗ₜ[ℂ] ground
  refine ⟨⟨0, 0, 0, -1, vacuum⟩, second, ?_⟩
  change tensorPairing ((Ytw data determinantUnit
    (Finsupp.single 0 (MvPolynomial.X (0, 0)))).coeff (-1) vacuum) second ≠ 0
  rw [Ytw_current]
  have creation : (tensorCurrentField data (ActualGround data determinantUnit) 0).coeff
      (-1) vacuum = created := by
    change tensorEnd data NativeGround (currentCoeff data 0 (-1)) vacuum = created
    norm_num [currentCoeff, tensorEnd, _root_.D5.S3.VertexAlgebra.LatticeHalfFock.current,
      vacuum, created]
  rw [creation]
  exact nonzero

def altered (selected : Role) : Realization signature :=
  realize signature (fun role parameter state =>
    if role = selected then (1 : ℂ) else actual.readout role parameter state)
    (fun empty => nomatch empty)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨parameter, state, nonzero⟩ := source_nonzero
  refine ⟨parameter, state, 0, ?_⟩
  rw [actual_readout, actual_readout]
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
      have impossible := law 0 0 0 0 0 0
      cases role
      · change (1 : ℂ) = actual.readout Role.reflected ⟨0, 0, 0, 0, 0⟩ 0 at impossible
        rw [actual_readout] at impossible
        simpa [originalReadout] using impossible
      · change actual.readout Role.original ⟨0, 0, 0, 0, 0⟩ 0 = (1 : ℂ) at impossible
        rw [actual_readout] at impossible
        simpa [originalReadout] using impossible
  · intro empty
    exact nomatch empty

def familyRegistration : Registration arena (type_of% (@original_jet_source_reflection)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp original_jet_source_reflection, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def escapeFrom := @Ytw

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_jet_source_reflection)
    (type_of% (realize signature actual.readout actual.anchor)) (type_of% escapeFrom) Role where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockBpZ.original_jet_source_reflection
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeReflection.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeReflection
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
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


namespace Word

abbrev Parameters := Σ _charge : Charge data, Σ count : ℕ,
  Σ _axes : Fin count → Fin data.rank, Σ _orders : Fin count → ℕ,
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
  let ⟨charge, count, axes, orders, exponent, first⟩ := parameter
  tensorPairing ((Ytw data determinantUnit (Finsupp.single charge
    (∏ j : Fin count, MvPolynomial.X (axes j, orders j)))).coeff exponent first) state

def reflectedReadout (parameter : Parameters) (state : NativeTensor) : ℂ :=
  let ⟨charge, count, axes, orders, exponent, first⟩ := parameter
  let weight : ℕ := ∑ j : Fin count, (orders j + 1)
  (-1 : ℂ) ^ weight * ∑ selection : ((j : Fin count) → Fin (orders j + 2)),
    (∏ j : Fin count, ((orders j + 1).choose (selection j).val : ℂ)) *
      tensorPairing first ((nativeOppositeYtw (Finsupp.single charge
        (∏ j : Fin count, if (selection j).val = 0 then
          MvPolynomial.C (bilinear data (unitCharge data (axes j)) charge : ℂ)
        else MvPolynomial.X (axes j, (selection j).val - 1)))).coeff
          (-2 * chargeNorm data charge - exponent - 2 * (weight : ℤ) -
            2 * (∑ j : Fin count, ((selection j).val : ℤ))) state)

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
  Law observation := ∀ (charge : Charge data) (count : ℕ)
    (axes : Fin count → Fin data.rank) (orders : Fin count → ℕ)
    (exponent : ℤ) (first second : NativeTensor),
    let _weight : ℕ := ∑ j : Fin count, (orders j + 1)
    observation.readout Role.original ⟨charge, count, axes, orders, exponent, first⟩ second =
      observation.readout Role.reflected ⟨charge, count, axes, orders, exponent, first⟩ second

theorem exact_source_bridge :
    (type_of% (@original_word_source_reflection)) ↔ arena.Law actual := by
  exact Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact one_ne_zero (law 0 0 Fin.elim0 Fin.elim0 0 0 0)

private theorem actual_readout (role : Role) (parameter : Parameters) (state : NativeTensor) :
    actual.readout role parameter state = originalReadout parameter state := by
  rcases parameter with ⟨charge, count, axes, orders, exponent, first⟩
  cases role
  · rfl
  · exact (original_word_source_reflection charge count axes orders exponent first state).symm

private theorem source_nonzero : ∃ parameter state, originalReadout parameter state ≠ 0 := by
  obtain ⟨⟨charge, axis, order, exponent, first⟩, state, nonzero⟩ :=
    Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeReflection.source_nonzero
  refine ⟨⟨charge, 1, fun _ => axis, fun _ => order, exponent, first⟩, state, ?_⟩
  simpa only [originalReadout,
    Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeReflection.originalReadout,
    Fin.prod_univ_one] using nonzero

def altered (selected : Role) : Realization signature :=
  realize signature (fun role parameter state =>
    if role = selected then (1 : ℂ) else actual.readout role parameter state)
    (fun empty => nomatch empty)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨parameter, state, nonzero⟩ := source_nonzero
  refine ⟨parameter, state, 0, ?_⟩
  rw [actual_readout, actual_readout]
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
      have impossible := law 0 0 Fin.elim0 Fin.elim0 0 0 0
      cases role
      · change (1 : ℂ) = actual.readout Role.reflected ⟨0, 0, Fin.elim0, Fin.elim0, 0, 0⟩ 0
          at impossible
        rw [actual_readout] at impossible
        simpa [originalReadout] using impossible
      · change actual.readout Role.original ⟨0, 0, Fin.elim0, Fin.elim0, 0, 0⟩ 0 = (1 : ℂ)
          at impossible
        rw [actual_readout] at impossible
        simpa [originalReadout] using impossible
  · intro empty
    exact nomatch empty

def familyRegistration : Registration arena (type_of% (@original_word_source_reflection)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp original_word_source_reflection, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def escapeFrom := @Ytw

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_word_source_reflection)
    (type_of% (realize signature actual.readout actual.anchor)) (type_of% escapeFrom) Role where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockBpZ.original_word_source_reflection
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeReflection.Word.familyRegistration
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeReflection
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms familyRegistration

end Word

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.NativeReflection
