import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPrefixRigidity
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPrefixRigidity

universe u
open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout paid)
open ActualFiniteObserverAbsentElimination
open Observer.ActualObserverPrefixRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := RawHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := RawHistory
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ h => h) (fun e => nomatch e)

abbrev replayArena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [Fintype E] (M : Observer E) (U V : Source)
    {e : E} {h : RawHistory}, ActualPrefix M U e h →
    (∀ q ∈ paid h, readout q V = readout q U) →
    ActualPrefix M V e (R.readout () () h)

abbrev rigidityArena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [Fintype E] (M : Observer E) (U V : Source),
    Legal M U → ∀ {e : E} {h h' t : RawHistory} {f : E} {b : Bool},
    ActualPrefix M U e h → ActualPrefix M V e h' →
    CacheTruth (M.decoder e) V → Run M V M.e0 t f b → R.readout () () h = h'

theorem replay_bridge : (type_of% (@actualPrefix_replay.{u})) ↔ replayArena.{u}.Law actual := Iff.rfl

theorem rigidity_bridge : (type_of% (@actualPrefix_history_rigid.{u})) ↔
    rigidityArena.{u}.Law actual := Iff.rfl

theorem replay_law : replayArena.{u}.Law actual := @actualPrefix_replay.{u}

theorem rigidity_law : rigidityArena.{u}.Law actual := @actualPrefix_history_rigid.{u}

private def halted : Observer (ULift.{u} Unit) where
  e0 := ⟨()⟩
  action _ := .inr false
  transition e _ := e
  decoder _ := []
  decoded_nodup _ := by simp

private theorem halted_legal (U : Source) : Legal halted.{u} U := by
  refine ⟨rfl, ?_⟩
  intro e h pref
  refine ⟨by simp [CacheTruth, halted], ?_⟩
  intro q row
  cases row

noncomputable def bad : Realization signature :=
  realize signature (fun _ _ _ => [⟨[], Reply.absent⟩]) (fun e => nomatch e)

theorem replay_bad : ¬ replayArena.{u}.Law bad := by
  intro law
  have pref := law halted (.of false) (.of false)
    (h := []) ActualPrefix.initial (by simp [paid])
  change ActualPrefix halted (.of false) halted.e0 [⟨[], Reply.absent⟩] at pref
  have empty : ∀ {e : ULift.{u} Unit} {h : RawHistory},
      ActualPrefix halted (.of false) e h → h = [] := by
    intro e h pref
    induction pref with
    | initial => rfl
    | query prior row ih => cases row
  have impossible := empty pref
  cases impossible

theorem rigidity_bad : ¬ rigidityArena.{u}.Law bad := by
  intro law
  have equation := law halted (.of false) (.of false) (halted_legal _) (h := [])
    (h' := []) ActualPrefix.initial ActualPrefix.initial
    (by simp [CacheTruth, halted]) (Run.halt (b := false) rfl)
  change ([⟨[], Reply.absent⟩] : RawHistory) = [] at equation
  cases equation

theorem replay_variation : Variation replayArena.{u} actual := ⟨replay_law, bad, replay_bad⟩

theorem rigidity_variation : Variation rigidityArena.{u} actual := ⟨rigidity_law, bad, rigidity_bad⟩

theorem replay_sensitivity : Sensitivity replayArena.{u} actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, replay_bad⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

theorem rigidity_sensitivity : Sensitivity rigidityArena.{u} actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, rigidity_bad⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), [], [⟨[], Reply.absent⟩], by simp [actual, realize]⟩

noncomputable def replayFamily : Registration replayArena.{u} (type_of% (@actualPrefix_replay.{u})) where
  actual := actual
  bridge := replay_bridge
  variation := replay_variation
  sensitivity := replay_sensitivity
  dependence := dependence

noncomputable def rigidityFamily : Registration rigidityArena.{u}
    (type_of% (@actualPrefix_history_rigid.{u})) where
  actual := actual
  bridge := rigidity_bridge
  variation := rigidity_variation
  sensitivity := rigidity_sensitivity
  dependence := dependence

noncomputable def replayRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@actualPrefix_replay.{u}) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPrefixRigidity.replayUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPrefixRigidity.replayFamily
  realizationSource := none
  generated := false
  arena := .source ⟨replayArena⟩
  objectArena := .source ⟨replayArena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source replayArena ⟨replayFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPrefixRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms replayFamily
#print axioms replayRegistration

noncomputable def rigidityRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@actualPrefix_history_rigid.{u}) (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPrefixRigidity.rigidityUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPrefixRigidity.rigidityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rigidityArena⟩
  objectArena := .source ⟨rigidityArena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source rigidityArena ⟨rigidityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPrefixRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms rigidityFamily
#print axioms rigidityRegistration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPrefixRigidity
