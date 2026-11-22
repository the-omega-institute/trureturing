import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock
import Reg.Support.DependentFamily

/-! The actual next source-owned bit at the paid birth cursor. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Nat
  State _ := BirthStream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ i z => consume z i) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (z : BirthStream) (n : Nat),
    (∀ i (e : BirthEvent), (physicalBirthClock z n).births[i]? = some e →
      F.readout () i z = e.mark ∧ e.serial = i + 1) ∧
    After n (physicalBirthClock z n).tree ∧
    Step (physicalBirthClock z n).tree (physicalBirthClock z (n+1)).tree ∧
    (physicalBirthClock z n).cursor = (physicalBirthClock z n).births.length ∧
    (physicalBirthClock z n).births.length = clockSum n ∧
    (physicalBirthClock z n).births.length = Nat.fib (n+1) - 1 ∧
    (physicalBirthClock z n).births.Pairwise chronologicallyBefore ∧
    (∃ batch : List BirthEvent,
      (physicalBirthClock z (n+1)).births = (physicalBirthClock z n).births ++ batch ∧
      (∀ e ∈ batch, e.update = n+1) ∧
      (∀ e, e ∈ (physicalBirthClock z n).births ↔
        e ∈ (physicalBirthClock z (n+1)).births ∧ e.update < n+1)) ∧
    (2 ≤ n →
      (physicalBirthClock z (n-1)).births.length = Nat.fib n - 1 ∧
      (physicalBirthClock z n).births.length -
        (physicalBirthClock z (n-1)).births.length = Nat.fib (n-1) ∧
      alphaLeaves (physicalBirthClock z n).tree = Nat.fib (n-1) ∧
      betaLeaves (physicalBirthClock z n).tree = Nat.fib n) ∧
    (let old := physicalBirthClock z n
     let r := birthRound z (n+1) old.cursor [] old.tree
     r.births.length = Nat.fib n ∧
     (r.births.map BirthEvent.parent).Nodup ∧
     (∀ p, p ∈ r.births.map BirthEvent.parent ↔ isBeta old.tree p = true) ∧
     (∀ e ∈ r.births, e.update = n+1 ∧ atTree r.tree e.parent =
       some (if e.mark then .mul beta alpha else .mul alpha beta))) ∧
    (∀ z' : BirthStream, (∀ j, 1 ≤ j → j ≤ (physicalBirthClock z n).cursor → z j = z' j) →
      physicalBirthClock z n = physicalBirthClock z' n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : (physicalBirthClock (fun _ => true) 2).births[0]? =
      some ⟨1, 2, [], true⟩ := rfl
  have hf := ((h (fun _ => true) 2).1 0 _ he).1
  cases hf

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨0, fun _ => true, fun _ => false, fun h => Bool.noConfusion h⟩

def family : Registration arena (type_of% physical_birth_clock) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨physical_birth_clock, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    physical_birth_clock (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock
