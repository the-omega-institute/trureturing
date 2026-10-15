import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.GradedDual
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency true

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.GradedDual

open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockBpZ
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockIntegralOddFixedSector
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

inductive Role where
  | dual
  | pairing
  deriving DecidableEq

instance : Fintype Role where
  elems := {Role.dual, Role.pairing}
  complete role := by cases role <;> simp

instance : Nonempty Role := ⟨Role.dual⟩

abbrev Parameters := Σ spectrum : LeechNativeSpectrum,
  Σ grade : ℤ, integralSector spectrum grade

abbrev signature : Signature where
  Params := Parameters
  State _ := NativeW
  Role := Role
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role parameter state => match role with
    | .dual => gradedWSelfDuality parameter.1 state parameter.2.1 parameter.2.2
    | .pairing => tensorPairing state.val parameter.2.2.val)
    (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun role _ _ => match role with
    | .dual => (1 : ℂ)
    | .pairing => (0 : ℂ)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter state,
    observation.readout Role.dual parameter state =
      observation.readout Role.pairing parameter state

theorem exact_source_bridge :
    (type_of% (@graded_w_self_duality_evaluation)) ↔ arena.Law actual := by
  constructor
  · intro source parameter state
    exact source parameter.1 state parameter.2.1 parameter.2.2
  · intro law spectrum state value test
    exact law ⟨spectrum, value, test⟩ state

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have impossible := law ⟨explicitLeechSpectrum, 2, 0⟩ (0 : NativeW)
  change (1 : ℂ) = 0 at impossible
  exact one_ne_zero impossible

private theorem actual_readout (role : Role) (parameter : Parameters) (state : NativeW) :
    actual.readout role parameter state = tensorPairing state.val parameter.2.2.val := by
  cases role
  · exact graded_w_self_duality_evaluation parameter.1 state parameter.2.1 parameter.2.2
  · rfl

def altered (selected : Role) : Realization signature :=
  realize signature (fun (role : Role) parameter state =>
    if role = selected then (1 : ℂ) else actual.readout role parameter state)
    (fun empty => nomatch empty)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  change Role at role
  let spectrum := explicitLeechSpectrum
  let Grade := integralSector spectrum 2
  have dimension : Module.finrank ℂ Grade = 98304 := by
    change Module.finrank ℂ (integralSector spectrum 2) = _
    rw [integralSector_eq_native_eigenspace]
    exact spectrum.dimension
  have nontrivial : Nontrivial Grade := Module.nontrivial_of_finrank_pos (by
    rw [dimension]
    norm_num)
  letI := nontrivial
  obtain ⟨state, nonzero⟩ := exists_ne (0 : Grade)
  have separating := integral_pairing_nondegenerate spectrum 2
  have witness : ∃ test : Grade, integralPairing spectrum 2 state test ≠ 0 := by
    by_contra missing
    apply nonzero
    apply separating.1
    intro test
    exact not_ne_iff.mp (fun different => missing ⟨test, different⟩)
  obtain ⟨test, different⟩ := witness
  let oddState : NativeW := ⟨state.val, state.property.1⟩
  refine ⟨⟨spectrum, 2, test⟩, oddState, (0 : NativeW), ?_⟩
  intro equality
  have firstReadout := actual_readout role ⟨spectrum, 2, test⟩ oddState
  have zeroReadout := actual_readout role ⟨spectrum, 2, test⟩ (0 : NativeW)
  rw [firstReadout, zeroReadout] at equality
  change tensorPairing state.val test.val = tensorPairing 0 test.val at equality
  simp only [map_zero] at equality
  exact different equality

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
      cases role <;> cases other
      · exact (different rfl).elim
      · rfl
      · rfl
      · exact (different rfl).elim
    · intro law
      have impossible := law ⟨explicitLeechSpectrum, 2, 0⟩ (0 : NativeW)
      have zeroPair : tensorPairing (0 : NativeTensor) (0 : NativeTensor) = 0 :=
        congrArg (fun functional : NativeTensor →ₗ[ℂ] ℂ => functional 0)
          (map_zero tensorPairing)
      cases role
      · change (1 : ℂ) =
          actual.readout Role.pairing ⟨explicitLeechSpectrum, 2, 0⟩ (0 : NativeW) at impossible
        rw [actual_readout] at impossible
        change (1 : ℂ) = tensorPairing (0 : NativeTensor) (0 : NativeTensor) at impossible
        rw [zeroPair] at impossible
        exact one_ne_zero impossible
      · change actual.readout Role.dual ⟨explicitLeechSpectrum, 2, 0⟩ (0 : NativeW) =
          (1 : ℂ) at impossible
        rw [actual_readout] at impossible
        change tensorPairing (0 : NativeTensor) (0 : NativeTensor) = (1 : ℂ) at impossible
        rw [zeroPair] at impossible
        exact zero_ne_one impossible
  · intro empty
    exact nomatch empty

def familyRegistration : Registration arena
    (type_of% (@graded_w_self_duality_evaluation)) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.mp graded_w_self_duality_evaluation,
    rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def escapeFrom := @gradedWSelfDuality

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@graded_w_self_duality_evaluation)
    (type_of% (realize signature actual.readout actual.anchor)) (type_of% escapeFrom) Role where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockBpZ.graded_w_self_duality_evaluation
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.GradedDual.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun role parameter state => match role with
    | .dual => gradedWSelfDuality parameter.1 state parameter.2.1 parameter.2.2
    | .pairing => tensorPairing state.val parameter.2.2.val)
    (fun empty => nomatch empty))
  variation := .evidence ⟨familyRegistration.variation⟩ trivial
  sensitivity := .evidence ⟨familyRegistration.sensitivity⟩ trivial
  partialSensitivity := none
  escapeFrom := some escapeFrom
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockBpZ.GradedDual
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := some ⟨arena, ⟨familyRegistration⟩⟩
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms familyRegistration

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockBpZ.GradedDual
