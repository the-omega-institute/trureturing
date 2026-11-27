import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisition
import Reg.Support.DependentFamily

/-! Source-equivalent registration of the actual native readout. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisition

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisition
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring
open LocalTwoStepRecognizer KnownSeedCurrentFibers PhysicalBirthClock OrderedBirthPrefix
open PublicRowSeedReadiness LawfulSourceReadiness NativePastAcquisitionBarrier

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Promise
  State _ := OutputStream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => (acquire p w).earned) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (P : Promise) (_hP : P.Valid) (s : OutputStream) (_hs : P.Legal s),
    F.readout () P s = prefixBits (birthOf s) P.target ∧
    let m := P.target
    let N := deadline m
    let a := acquire P s
    let addresses := ((physicalBirthClock (birthOf s) (N-1)).births.take m).map
      (fun e => e.parent ++ [false,false])
    a.cut = N ∧ installEarned a = some s ∧
    acquiredAnswers a = some (physicalTree N s, fun p => queryNext N p s, future N s) ∧
    a.addresses = addresses ∧ a.reads = m ∧ a.updates = N ∧
    a.weight = (addresses.map List.length).sum ∧
    a.maximum = (addresses.map List.length).foldl max 0 ∧
    a.weight ≤ m * (N-1) ∧ a.maximum ≤ N-1 ∧
    (m = 0 → N = 2 ∧ a.reads = 0 ∧ a.weight = 0 ∧ a.maximum = 0 ∧ ∀ i, s i = false) ∧
    (0 < m → 3 ≤ N ∧ m ≤ Nat.fib N - 1 ∧
      ∀ n, 3 ≤ n → m ≤ Nat.fib n - 1 → N ≤ n) ∧
    a.completionRecorded P ∧ a.result.nextIndex = clockSum N ∧
    (∃ k, let r := run planObserver (acquisitionPlan P m N) () s k
      r.stopped = true ∧ r.cut = a.cut ∧ r.register.1 = .stop a.earned a.result ∧
        r.log.filterMap nativeService = a.events.filterMap planService)

private def rowOne : Promise := .row 1 (fun _ => false)

private def rowBit (b : Bool) : OutputStream := rowStream (r := 1) (fun _ => false) (fun _ => b)

private theorem rowBit_prefix (b : Bool) : prefixBits (birthOf (rowBit b)) 1 = [b] := by
  change [rowBit b 0] = [b]
  unfold rowBit
  rw [rowStream]
  simp

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h rowOne trivial (rowBit true) ⟨fun _ => true,rfl⟩).1
  change [] = prefixBits (birthOf (rowBit true)) 1 at hbad
  rw [rowBit_prefix] at hbad
  cases hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨rowOne, rowBit false, rowBit true, ?_⟩
  change (acquire rowOne (rowBit false)).earned ≠ (acquire rowOne (rowBit true)).earned
  rw [(attained_prefix_acquisition rowOne trivial (rowBit false) ⟨fun _ => false,rfl⟩).1,
    (attained_prefix_acquisition rowOne trivial (rowBit true) ⟨fun _ => true,rfl⟩).1]
  change prefixBits (birthOf (rowBit false)) 1 ≠ prefixBits (birthOf (rowBit true)) 1
  rw [rowBit_prefix, rowBit_prefix]
  decide

def family : Registration arena (type_of% attained_prefix_acquisition) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨attained_prefix_acquisition, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@attained_prefix_acquisition) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisition.unit
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisition.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisition
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisition
