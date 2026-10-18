import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.FiniteRealZeroFillRegister
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Observer.Linear.FiniteRealZeroFillRegister
open _root_.D5.S3.Observer.Linear.FiniteRealZeroFillRegister
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev iterateSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ State State

def iterateActual : Realization iterateSignature :=
  realize iterateSignature (fun _ _ q => q) (fun e => nomatch e)

def iterateRejected : Realization iterateSignature :=
  realize iterateSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev iterateArena : Arena where
  signature := iterateSignature
  Law r := ∀ (H t : ℕ) (q : State H) (i : Fin (H + 1)) (hi : i.val + t < H + 1),
    (update H : State H → State H)^[t] (r.readout () H q) i = q ⟨i.val + t, hi⟩

private theorem iterateRejectedLaw : ¬ iterateArena.Law iterateRejected := by
  intro h
  have hh := h 0 0 (fun _ => 1) 0 (by decide)
  change (0 : ℝ) = 1 at hh
  exact zero_ne_one hh

private theorem iterateDependence : ObservationalDependence iterateSignature iterateActual := by
  intro role
  refine ⟨0, 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  change (0 : ℝ) = 1 at hh
  exact zero_ne_one hh

def iterateSource : Registration iterateArena (type_of% @update_iterate) where
  actual := iterateActual
  bridge := Iff.rfl
  variation := ⟨update_iterate, iterateRejected, iterateRejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ iterateRejectedLaw
  dependence := iterateDependence

def iterateRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@update_iterate) (Realization iterateSignature) (ℕ → Type) Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.FiniteRealZeroFillRegister.iterateUnit
  realizationName := `Reg.D5.S3.Observer.Linear.FiniteRealZeroFillRegister.iterateSource
  realizationSource := none
  generated := false
  arena := .source ⟨iterateArena⟩
  objectArena := .source ⟨iterateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source iterateArena ⟨iterateSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize iterateSignature (fun _ _ q => q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some State
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.FiniteRealZeroFillRegister
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev pointwiseSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => X) State

def pointwiseActual : Realization pointwiseSignature :=
  realize pointwiseSignature (fun _ H x => initState H x) (fun e => nomatch e)

def pointwiseRejected : Realization pointwiseSignature :=
  realize pointwiseSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev pointwiseArena : Arena where
  signature := pointwiseSignature
  Law r := ∀ (H : ℕ) (x : X) (t : ℕ) (ht : t ≤ H),
    readout H ((update H : State H → State H)^[t] (r.readout () H x)) = signal t x

private theorem pointwiseRejectedLaw : ¬ pointwiseArena.Law pointwiseRejected := by
  intro h
  have hh := h 0 (fun _ => false) 0 (by decide)
  norm_num [pointwiseRejected, realize, readout, signal, bitSign] at hh

private theorem pointwiseDependence : ObservationalDependence pointwiseSignature pointwiseActual := by
  intro role
  refine ⟨0, (fun _ => false), (fun _ => true), ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [pointwiseActual, realize, initState, signal, bitSign] at hh

def pointwiseSource : Registration pointwiseArena (type_of% @pointwise_attainment) where
  actual := pointwiseActual
  bridge := Iff.rfl
  variation := ⟨pointwise_attainment, pointwiseRejected, pointwiseRejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ pointwiseRejectedLaw
  dependence := pointwiseDependence

def pointwiseRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@pointwise_attainment) (Realization pointwiseSignature) Type Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.FiniteRealZeroFillRegister.pointwiseUnit
  realizationName := `Reg.D5.S3.Observer.Linear.FiniteRealZeroFillRegister.pointwiseSource
  realizationSource := none
  generated := false
  arena := .source ⟨pointwiseArena⟩
  objectArena := .source ⟨pointwiseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pointwiseArena ⟨pointwiseSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pointwiseSignature (fun _ H x => initState H x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some X
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.FiniteRealZeroFillRegister
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms iterateSource
#print axioms pointwiseSource
#print axioms iterateRegistration
#print axioms pointwiseRegistration
end
end Reg.D5.S3.Observer.Linear.FiniteRealZeroFillRegister
