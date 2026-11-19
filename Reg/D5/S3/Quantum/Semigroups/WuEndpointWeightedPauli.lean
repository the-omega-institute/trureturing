import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuEndpointWeightedPauli

/-! Source-bound readouts for the weighted Pauli formula and twirl. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.WuRankOneEndpointFloor

namespace Reg.D5.S3.Quantum.Semigroups.WuEndpointWeightedPauli

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => TwoMode)
    (fun _ => TwoMode → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (one_ne_zero : (1 : TwoMode) ≠ 0) (Eq.mp (congrFun h 0) rfl)

namespace PauliTwirl

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ X : TwoMode,
    R.readout () () (endpointConjugationSum 1 1 X) ((4 * X.trace) • (1 : TwoMode))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0

def family : Registration arena (type_of% @endpoint_pauli_twirl) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@endpoint_pauli_twirl, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpoint_pauli_twirl) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointWeightedPauli.endpoint_pauli_twirl.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointWeightedPauli.PauliTwirl.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointWeightedPauli
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PauliTwirl

namespace WeightedPauli

private abbrev EndpointMap := TwoMode →ₗ[ℂ] TwoMode

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => EndpointMap)
    (fun _ => EndpointMap → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, LinearMap.id, ?_⟩
  intro h
  have he : (LinearMap.id : EndpointMap) = 0 := Eq.mp (congrFun h 0) rfl
  have hm := DFunLike.congr_fun he (1 : TwoMode)
  exact (one_ne_zero : (1 : TwoMode) ≠ 0) (by simpa using hm)

private abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () A₁ (endpointConjugationSum (endpointAlpha : ℂ) (endpointBeta : ℂ))

private theorem rejected_law : ¬ arena.Law rejected := by
  exact fun h => h

def family : Registration arena (type_of% @A1_eq_weighted_pauli) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A1_eq_weighted_pauli, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A1_eq_weighted_pauli) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointWeightedPauli.A1_eq_weighted_pauli.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointWeightedPauli.WeightedPauli.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointWeightedPauli
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end WeightedPauli

end Reg.D5.S3.Quantum.Semigroups.WuEndpointWeightedPauli
