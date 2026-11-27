import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.NativePastAcquisitionBarrier
import Reg.Support.DependentFamily

/-! Source-equivalent registration of an actual presence reply at an observed cut. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.NativePastAcquisitionBarrier

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.NativePastAcquisitionBarrier
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring
open LocalTwoStepRecognizer KnownSeedCurrentFibers PhysicalBirthClock
open PublicRowSeedReadiness LawfulSourceReadiness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : Nat, Action
  State _ := BirthStream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => reply z p.1 p.2) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .ack) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (n : Nat) (s t : OutputStream)
      {Public Tape Local : Type} (A : Observer Public Tape Local) (u : Public),
    (∀ (e : Nat) (a : Action), e ≤ n → matureWord n s = matureWord n t →
      F.readout () ⟨e, a⟩ (birthOf s) = reply (birthOf t) e a) ∧
    (∀ (tape : Tape) (k : Nat), (run A u tape s k).cut ≤ n →
      run A u tape s k = replay A u tape (matureWord n s) k) ∧
    (matureWord n s = matureWord n t →
      (∀ (tape : Tape) (k : Nat), (run A u tape s k).cut ≤ n →
        run A u tape s k = run A u tape t k) ∧
      ∀ E : Set (Record Local), cutEvent A u s n E = cutEvent A u t n E) ∧
    (∀ (C : LawfulClass), ValidClass C → 2 ≤ n → matureSize n < requiredBits C →
      ∀ (F : Filter Tape) [Filter.NeBot F]
        (labels : Public → Tape → Record Local → Option Labelled)
        (next : Public → Tape → Record Local → Option (Address → Bool))
        (behavior : Public → Tape → Record Local → Option FutureBehavior),
      (¬ ZeroErrorAt F A u C n labels (physicalTree n)) ∧
      (¬ ZeroErrorAt F A u C n next (fun w p => queryNext n p w)) ∧
      (¬ ZeroErrorAt F A u C n behavior (future n)))

private def readingObserver : Observer Unit Unit Unit where
  startState _ _ := ()
  choose _ _ _ := .service (.read [])

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let z : OutputStream := fun _ => false
  have hbad := (h 0 z z readingObserver ()).1 0 (.read []) (by decide) rfl
  change Reply.ack = Reply.answer true at hbad
  cases hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨3, .read [false, false]⟩, fun _ => false, fun _ => true, ?_⟩
  change reply (fun _ => false) 3 (.read [false,false]) ≠
    reply (fun _ => true) 3 (.read [false,false])
  decide

def family : Registration arena (type_of% native_past_acquisition_barrier) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_past_acquisition_barrier, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_past_acquisition_barrier) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.NativePastAcquisitionBarrier.unit
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.NativePastAcquisitionBarrier.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.NativePastAcquisitionBarrier
    definition := none
    coordinates := #[8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.NativePastAcquisitionBarrier
