import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace PrefixFree
abbrev signature : Signature where
  Params := Unit
  State _ := Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Address
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ a => a) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ ⦃a : Address⦄, a ∈ (P : Set Address) →
    ∀ ⦃b : Address⦄, b ∈ (P : Set Address) → a <+: b → R.readout () () a = b
private theorem badLaw : ¬ arena.Law bad := by
  intro h
  have member : position 0 ∈ (P : Set Address) := by
    exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
  have eq := @h (position 0) member (position 0) member (List.prefix_refl _)
  change [] = position 0 at eq
  exact (by decide : ([] : Address) ≠ position 0) eq
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),position 0,position 1,?_⟩
  change position 0 ≠ position 1
  decide
def family : Registration arena (type_of% (@prefix_free)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prefix_free,bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prefix_free)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.prefix_free.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.PrefixFree.family
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms registration
end PrefixFree

namespace Realization
abbrev signature : Signature where
  Params := Unit
  State _ := Fin 6
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ z => canonicalRow P (origin z)) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => row) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := (∀ z : Fin 6, substitution (origin z) = current z ∧
    canonicalRow P (current z) = row ∧ R.readout () () z = predecessor (label z)) ∧
    Function.Injective predecessor
private theorem badLaw : ¬ arena.Law bad := by
  intro h
  have eq := (h.1 2).2.2
  change row = predecessor (label 2) at eq
  exact (by decide : row ≠ predecessor (label 2)) eq
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,2,?_⟩
  change canonicalRow P (origin 0) ≠ canonicalRow P (origin 2)
  rw [(six_source_realization.1 0).2.2,(six_source_realization.1 2).2.2]
  decide
def family : Registration arena (type_of% (@six_source_realization)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨six_source_realization,bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@six_source_realization)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.six_source_realization.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.Realization.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn","arg","body","arg","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms registration
end Realization

namespace Occurrence
abbrev signature : Signature where
  Params := Fin 8 × Address
  State _ := Fin 6
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ p z => readout (position p.1 ++ p.2) (current z)) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => Reply.alpha) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Fin 8) (w : Address) (z : Fin 6),
    R.readout () (p,w) z = readout w (values z (occurrenceClass p))
private theorem badLaw : ¬ arena.Law bad := by
  intro h
  have eq := h 0 [] 0
  change Reply.alpha = Reply.beta at eq
  cases eq
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0,[]),0,1,?_⟩
  change readout (position 0 ++ []) (current 0) ≠ readout (position 0 ++ []) (current 1)
  decide
def family : Registration arena (type_of% (@occurrence_read)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨occurrence_read,bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@occurrence_read)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.occurrence_read.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.Occurrence.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms registration
end Occurrence

namespace Factor
abbrev signature : Signature where
  Params := Address
  State _ := Fin 6
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ a z => readout a (current z)) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ z => if z = 0 then Reply.alpha else Reply.beta) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ a : Address, ∃ f : Bool → Reply,
    ∀ z : Fin 6, R.readout () a z = f (question a z)
private theorem badLaw : ¬ arena.Law bad := by
  intro h
  obtain ⟨f,hf⟩ := h []
  have a := hf 0
  have b := hf 1
  change Reply.alpha = f false at a
  change Reply.beta = f false at b
  have eq := a.trans b.symm
  cases eq
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨position 0,0,1,?_⟩
  change readout (position 0) (current 0) ≠ readout (position 0) (current 1)
  decide
def family : Registration arena (type_of% (@all_address_factor)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨all_address_factor,bad,badLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,badLaw⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@all_address_factor)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.all_address_factor.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones.Factor.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","arg","body","body","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms registration
end Factor
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones
