import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSelectedRA
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress

abbrev frontierSignature : Signature where
  Params := Source × (Nat → Bool)
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := World
  Anchor := Empty
  finiteAnchor := inferInstance

def frontierActual : Realization frontierSignature :=
  realize frontierSignature (fun _ p n => trajectory p.2 ⟨.entry,p.1,false⟩ n)
    (fun i => nomatch i)

def frontierBad : Realization frontierSignature :=
  realize frontierSignature
    (fun _ _ _ => ⟨.active false (go 99 emptyWork),.of true,false⟩)
    (fun i => nomatch i)

abbrev frontierArena : Arena where
  signature := frontierSignature
  Law R := ∀ (u : Source) (σ : Nat → Bool) (n : Nat),
    let w := R.readout () (u,σ) n
    Safe w.source w.config ∧
      ∀ (q : Bool) (v : Work), w.config = .active q v → v.pc.val ≠ 99

private theorem frontier_bad : ¬ frontierArena.Law frontierBad := by
  intro h
  have no := (h (.of true) (fun _ => false) 0).1
  simpa [frontierBad,realize,Safe,Frontier,go] using no

private theorem frontier_dependence :
    ObservationalDependence frontierSignature frontierActual := by
  intro i
  refine ⟨(.of false,fun _ => false),0,1,?_⟩
  intro e
  have no := congrArg World.config e
  simp [frontierActual,realize,trajectory,worldEvent,step,
    _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.readout] at no

def frontierProof : Registration frontierArena (type_of% (@reachable_scan_frontier)) where
  actual := frontierActual
  bridge := Iff.rfl
  variation := ⟨@reachable_scan_frontier,frontierBad,frontier_bad⟩
  sensitivity := ⟨fun i => ⟨frontierBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,frontier_bad⟩,fun i => nomatch i⟩
  dependence := frontier_dependence

noncomputable def reachable_scan_frontier_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress.reachable_scan_frontier)
      (Realization frontierSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress.reachable_scan_frontier
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress.frontierProof
  realizationSource := none
  generated := false
  arena := .source ⟨frontierArena⟩
  objectArena := .source ⟨frontierArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source frontierArena ⟨frontierProof⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize frontierSignature
    (fun _ p n => trajectory p.2 ⟨.entry,p.1,false⟩ n) (fun i => nomatch i))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn","arg","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeSelectedRAProgress
