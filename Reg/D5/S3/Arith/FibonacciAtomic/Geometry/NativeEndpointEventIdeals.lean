import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair (Call)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

@[reducible] def signature : Signature where
  Params := Σ _ : Bool, Source
  State _ := Set Call
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p I => cutTerm p.1 p.2 I) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => .of true) (fun e => nomatch e)

@[reducible] def guardArena : Arena where
  signature := signature
  Law R := ∀ (b : Bool) (t : Source) (I : Set Call), Born b t → Ideal b t I →
    ∀ e ∈ events b t, Guard e (R.readout () ⟨b,t⟩ I) ↔ Enabled b t I e

private theorem bad_guard : ¬ guardArena.Law bad := by
  classical
  intro h
  have hb : Born true (.of false) :=
    ⟨_root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair.betaFHistory.domain,
      by simp⟩
  have hI : Ideal true (.of false) {Call.promote []} := by
    constructor
    · intro e he
      simpa [events] using he
    · intro e he d hd _
      simpa [events] using he
  have hh := (h true (.of false) {Call.promote []} hb hI (.promote []) (by simp [events])).mp
    (show Guard (.promote []) (bad.readout () ⟨true,.of false⟩ {Call.promote []}) from rfl)
  exact hh.1 (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨true,.of false⟩, ∅, {Call.promote []}, ?_⟩
  simp [actual, realize, cutTerm]

def guardFamilyRegistration : Registration guardArena (type_of% guard_enabled) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨guard_enabled, bad, bad_guard⟩
  sensitivity := ⟨fun i => ⟨bad,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl, bad_guard⟩,
    fun e => nomatch e⟩
  dependence := dependence }

noncomputable def guardRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@guard_enabled) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals.guard_enabled "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals.guardFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨guardArena⟩
  objectArena := .source ⟨guardArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source guardArena ⟨guardFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2, functionOperand := false, stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

@[reducible] def runSignature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Call → Option Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actualRun : Realization runSignature :=
  realize runSignature (fun _ _ t =>
    _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair.run t)
    (fun e => nomatch e)
def badRun : Realization runSignature :=
  realize runSignature (fun _ _ _ _ => none) (fun e => nomatch e)

@[reducible] def historyArena : Arena where
  signature := runSignature
  Law R := ∀ (t : Source),
    _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition.D t →
    ∀ w : List Call, R.readout () () (.of true) w = some t ↔
      ∃ l : List (Event true t), l.map Subtype.val = w ∧
        _root_.D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity.ExtensionList
          ∅ Set.univ l

private theorem bad_history : ¬ historyArena.Law badRun := by
  intro h
  have hd := _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair.alphaRHistory.domain
  have ex := (all_histories (.of true) hd []).mp rfl
  have hh := (h (.of true) hd []).mpr ex
  change none = some (FreeMagma.of true : Source) at hh
  contradiction

private theorem run_dependence : ObservationalDependence runSignature actualRun := by
  intro i
  cases i
  refine ⟨(), .of true, .of false, ?_⟩
  intro h
  have hh := congrFun h []
  change some (FreeMagma.of true : Source) = some (.of false) at hh
  cases hh

def historyFamilyRegistration : Registration historyArena (type_of% all_histories) := {
  actual := actualRun
  bridge := Iff.rfl
  variation := ⟨all_histories, badRun, bad_history⟩
  sensitivity := ⟨fun i => ⟨badRun,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl, bad_history⟩,
    fun e => nomatch e⟩
  dependence := run_dependence }

noncomputable def historyRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@all_histories) (type_of% (realize runSignature actualRun.readout actualRun.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals.all_histories "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals.historyFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨historyArena⟩
  objectArena := .source ⟨historyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source historyArena ⟨historyFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize runSignature actualRun.readout actualRun.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals
