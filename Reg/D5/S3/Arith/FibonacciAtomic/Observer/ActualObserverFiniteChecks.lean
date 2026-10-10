import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteChecks
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteChecks
universe u
open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Reply finiteDecision Positive)
open ActualFiniteObserverAbsentElimination
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteChecks
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

structure Context where
  Carrier : Type u
  finite : Fintype Carrier
  source : Source

abbrev signature : Signature where
  Params := Context.{u}
  State p := @Observer p.Carrier p.finite
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature (fun _ p M => @sourceCheck p.Carrier p.finite M p.source)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (M : Observer E) (U : Source),
    R.readout () ⟨E, inferInstance, U⟩ M = true ↔ Legal M U ∧
      ∃ t f b, Run M U M.e0 t f b ∧ (b = true ↔ Positive U)

theorem bridge : (type_of% (@sourceCheck_iff.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
theorem actual_law : arena.{u}.Law actual.{u} := @sourceCheck_iff.{u}

private def haltObserver {E : Type u} [Fintype E] (e : E) (b : Bool) : Observer E where
  e0 := e
  action _ := .inr b
  transition e _ := e
  decoder _ := []
  decoded_nodup _ := List.nodup_nil

private theorem halt_check {E : Type u} [Fintype E] (e : E) (b : Bool) (U : Source) :
    sourceCheck (haltObserver e b) U = true ↔ b = finiteDecision U := by
  letI : Nonempty E := ⟨e⟩
  letI : Nonempty (Fin (Fintype.card E)) := ⟨⟨0, Fintype.card_pos⟩⟩
  rw [sourceCheck, decide_eq_true_eq]
  simp [SourceCertificate, haltObserver, CacheTruth]

noncomputable def bad : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) actual.anchor

theorem bad_law : ¬ arena.{u}.Law bad.{u} := by
  intro law
  let U : Source := .of true
  let E := ULift.{u} Unit
  let e : E := ⟨()⟩
  let M := haltObserver e (finiteDecision U)
  have yes : sourceCheck M U = true := (halt_check e _ U).mpr rfl
  have right := (sourceCheck_iff M U).mp yes
  exact Bool.false_ne_true ((law M U).mpr right)

theorem variation : Variation arena.{u} actual.{u} := ⟨actual_law, bad, bad_law⟩

theorem sensitivity : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨bad, ?_, rfl, bad_law⟩
    intro j different
    exact False.elim (different (Subsingleton.elim _ _))
  · intro i
    exact nomatch i

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  let U : Source := .of true
  let E := ULift.{u} Unit
  let e : E := ⟨()⟩
  let p : Context.{u} := ⟨E, inferInstance, U⟩
  refine ⟨p, haltObserver e (finiteDecision U), haltObserver e (!(finiteDecision U)), ?_⟩
  have good := (halt_check e (finiteDecision U) U).mpr rfl
  have wrong : sourceCheck (haltObserver e (!(finiteDecision U))) U ≠ true := by
    intro h
    have h' := (halt_check e (!(finiteDecision U)) U).mp h
    cases d : finiteDecision U <;> simp [d] at h'
  intro same
  change sourceCheck (haltObserver e (finiteDecision U)) U =
    sourceCheck (haltObserver e (!(finiteDecision U))) U at same
  exact wrong (same.symm.trans good)

noncomputable def familyRegistration : Registration arena.{u} (type_of% (@sourceCheck_iff.{u})) where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceCheck_iff.{u}) (type_of% (realize signature.{u} actual.readout actual.anchor)) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteChecks.sourceCheck_iff.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteChecks.familyRegistration
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
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteChecks, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := some ⟨_, ⟨familyRegistration⟩⟩
  options := #[]

#print axioms registration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteChecks
