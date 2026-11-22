import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.OrderedBirthPrefix
import Reg.Support.DependentFamily

/-! The mature chronological marked word is directly observed by the finite inverse. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.OrderedBirthPrefix

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.OrderedBirthPrefix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := Shape
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option (Nat × List BirthEvent)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => matureFromShape s) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (z : BirthStream) (n : Nat) (_hn : 2 ≤ n),
    let t := (physicalBirthClock z n).tree
    let s := shape t
    F.readout () () s = some (n, (physicalBirthClock z (n-1)).births) ∧
    (shapeFromIncidence (incidenceAddresses s)).bind epochFromShape = some n ∧
    (shapeFromFrontier (frontierAddresses s)).bind epochFromShape = some n ∧
    shapeFromIncidence (incidenceAddresses s) = some s ∧
    shapeFromFrontier (frontierAddresses s) = some s ∧
    (∀ p, (p ∈ incidenceAddresses s ↔ present s p = true) ∧
      (p ∈ frontierAddresses s ↔ atTree s p = some tip) ∧
      (p ∈ incidenceAddresses s ↔ ∃ q : Address, p ++ q ∈ frontierAddresses s) ∧
      (p ∈ frontierAddresses s ↔ p ∈ incidenceAddresses s ∧
        ∀ q : Address, p ++ q ∈ incidenceAddresses s → q = [])) ∧
    (∀ z' : BirthStream,
      ((∀ p, p ∈ incidenceAddresses s ↔
        p ∈ incidenceAddresses (shape (physicalBirthClock z' n).tree)) ↔
          prefixBits z (clockSum (n-1)) = prefixBits z' (clockSum (n-1))) ∧
      ((∀ p, p ∈ frontierAddresses s ↔
        p ∈ frontierAddresses (shape (physicalBirthClock z' n).tree)) ↔
          prefixBits z (clockSum (n-1)) = prefixBits z' (clockSum (n-1))) ∧
      (t = (physicalBirthClock z' n).tree ↔ prefixBits z (clockSum n) = prefixBits z' (clockSum n))) ∧
    (physicalBirthClock z n).births.take (clockSum (n-1)) = (physicalBirthClock z (n-1)).births ∧
    maturePrefix s = some (n, prefixBits z (clockSum (n-1))) ∧
    shapeOfPrefix n (prefixBits z (clockSum (n-1))) = s ∧
    completeFromLabelled t = some (n, (physicalBirthClock z n).births) ∧
    completePrefix t = some (n, prefixBits z (clockSum n)) ∧
    labelsOfPrefix n (prefixBits z (clockSum n)) = t ∧
    (∀ bits : List Bool, bits.length = clockSum (n-1) →
      maturePrefix (shapeOfPrefix n bits) = some (n, bits)) ∧
    (∀ bits : List Bool, bits.length = clockSum n →
      completePrefix (labelsOfPrefix n bits) = some (n, bits)) ∧
    (∀ z' : BirthStream, s = shape (physicalBirthClock z' n).tree →
      ∃ bits : List Bool, bits.length = Nat.fib (n-1) ∧
        prefixBits z' (clockSum n) = prefixBits z (clockSum (n-1)) ++ bits) ∧
    (∀ bits : List Bool, bits.length = Nat.fib (n-1) →
      ∃! w : Labelled, ∃ z' : BirthStream,
        (physicalBirthClock z' n).tree = w ∧ shape w = s ∧
        prefixBits z' (clockSum n) = prefixBits z (clockSum (n-1)) ++ bits)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h (fun _ => true) 2 (by decide)).1
  cases hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), shape (physicalBirthClock (fun _ => true) 3).tree,
    shape (physicalBirthClock (fun _ => false) 3).tree, ?_⟩
  intro h
  cases h

def family : Registration arena (type_of% exact_ordered_birth_prefix) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_ordered_birth_prefix, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exact_ordered_birth_prefix (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.OrderedBirthPrefix.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.OrderedBirthPrefix.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.OrderedBirthPrefix
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.OrderedBirthPrefix
