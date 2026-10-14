import Mathlib.Tactic.NormNum
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.History.Spacetime.HFMemberOccurrences
import Reg.Support.SingleDependentReadout

set_option autoImplicit false

namespace Reg.D5.S0.History.Spacetime.HFMemberOccurrences

open _root_.D5.S0.History.Spacetime
open HFEncoding HFMemberOccurrences ArchiveCarrier ArchiveEncoding CoordinateEncoding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
noncomputable section

abbrev hfSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature HF (fun _ => HF) (fun _ => Nat)

def hfActual : Realization hfSignature :=
  realize hfSignature (fun _ _ z => mass z) (fun e => nomatch e)

def hfRejected : Realization hfSignature :=
  realize hfSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem mass_dependence : ObservationalDependence hfSignature hfActual := by
  intro i
  refine ⟨natCode 0, natCode 0, natCode 1, ?_⟩
  simp only [hfActual, realize, mass_natCode]
  norm_num

abbrev equationArena : Arena where
  signature := hfSignature
  Law R := ∀ x : HF, R.readout () x x = 1 + ∑ y : ↥(members x), mass y.val

private theorem equation_rejected : ¬ equationArena.Law hfRejected := by
  intro h
  have hz := h (natCode 0)
  change 0 = 1 + _ at hz
  simp [Nat.one_add] at hz

def equationEvidence : Registration equationArena
    (∀ x : HF, mass x = 1 + ∑ y : ↥(members x), mass y.val) where
  actual := hfActual
  bridge := Iff.rfl
  variation := ⟨mass_eq, hfRejected, equation_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ equation_rejected
  dependence := mass_dependence

abbrev cardinalityArena : Arena where
  signature := hfSignature
  Law R := ∀ x : HF, Nat.card (Occurrence x) = R.readout () x x

private theorem cardinality_rejected : ¬ cardinalityArena.Law hfRejected := by
  intro h
  have hz := h (natCode 0)
  change Nat.card (Occurrence (natCode 0)) = 0 at hz
  rw [occurrence_card, mass_natCode] at hz
  norm_num at hz

def cardinalityEvidence : Registration cardinalityArena
    (∀ x : HF, Nat.card (Occurrence x) = mass x) where
  actual := hfActual
  bridge := Iff.rfl
  variation := ⟨occurrence_card, hfRejected, cardinality_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ cardinality_rejected
  dependence := mass_dependence

abbrev naturalSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Nat (fun _ => HF) (fun _ => Nat)

def naturalActual : Realization naturalSignature :=
  realize naturalSignature (fun _ _ z => mass z) (fun e => nomatch e)

def naturalRejected : Realization naturalSignature :=
  realize naturalSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev naturalArena : Arena where
  signature := naturalSignature
  Law R := ∀ n : Nat, R.readout () n (natCode n) = 2 ^ n

private theorem natural_rejected : ¬ naturalArena.Law naturalRejected := by
  intro h
  have hz := h 0
  change 0 = 2 ^ 0 at hz
  norm_num at hz

def naturalEvidence : Registration naturalArena (∀ n : Nat, mass (natCode n) = 2 ^ n) where
  actual := naturalActual
  bridge := Iff.rfl
  variation := ⟨mass_natCode, naturalRejected, natural_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ natural_rejected
  dependence := by
    intro i
    refine ⟨0, natCode 0, natCode 1, ?_⟩
    simp only [naturalActual, realize, mass_natCode]
    norm_num

abbrev archiveSignature : Signature where
  Params := Σ x : Rich 3, Σ _e : x.1.archive.Event, Nat
  State _ := HF
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def archiveActual : Realization archiveSignature :=
  realize archiveSignature (fun b _ z => if b then Nat.card (Occurrence z) else mass z)
    (fun e => nomatch e)

abbrev archiveArena : Arena where
  signature := archiveSignature
  Law R := ∀ (x : Rich 3) (e : x.1.archive.Event) (n : Nat),
    (x.1.archive.attributes e).source = FreeMagma.of n →
      2 ^ n ≤ R.readout false ⟨x, e, n⟩ (richCode x) ∧
      2 ^ n ≤ R.readout true ⟨x, e, n⟩ (richCode x)

def archiveRejected (b : Bool) : Realization archiveSignature :=
  realize archiveSignature (fun j p z => if j = b then 0 else archiveActual.readout j p z)
    (fun e => nomatch e)

private def sampleAttribute : Attributes 3 := ⟨0, fun _ => 0, false, FreeMagma.of 0⟩

private def sampleArchive : Archive 3 where
  events := {attributesCode sampleAttribute}
  attributes _ := sampleAttribute
  causal _ _ := False
  irrefl _ := id
  trans _ _ _ h := h.elim
  time_lt _ _ h := h.elim

private def sampleContext : Context 3 := ⟨sampleArchive, ∅⟩
private def sampleRich : Rich 3 := ⟨sampleContext, ⟨∅, Finset.Subset.refl _⟩⟩
private def sampleEvent : sampleRich.1.archive.Event :=
  ⟨attributesCode sampleAttribute, Finset.mem_singleton_self _⟩

private theorem archive_rejected (b : Bool) : ¬ archiveArena.Law (archiveRejected b) := by
  intro h
  have hz := h sampleRich sampleEvent 0 rfl
  cases b
  · have hzero := hz.1
    change 2 ^ 0 ≤ 0 at hzero
    norm_num at hzero
  · have hzero := hz.2
    change 2 ^ 0 ≤ 0 at hzero
    norm_num at hzero

def archiveEvidence : Registration archiveArena
    (∀ (x : Rich 3) (e : x.1.archive.Event) (n : Nat),
      (x.1.archive.attributes e).source = FreeMagma.of n →
      2 ^ n ≤ mass (richCode x) ∧ 2 ^ n ≤ Nat.card (Occurrence (richCode x))) where
  actual := archiveActual
  bridge := Iff.rfl
  variation := ⟨richCode_leaf_bound, archiveRejected false, archive_rejected false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨archiveRejected i, ?_, rfl, archive_rejected i⟩
      intro j hj
      funext p z
      simp [archiveRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := by
    intro b
    refine ⟨⟨sampleRich, sampleEvent, 0⟩, natCode 0, natCode 1, ?_⟩
    cases b <;> simp [archiveActual, realize, occurrence_card, mass_natCode]

def equationRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.History.Spacetime.HFMemberOccurrences.mass_eq)
    (type_of% (realize hfSignature (fun _ _ z => mass z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S0.History.Spacetime.HFMemberOccurrences.equationUnit
  realizationName := `Reg.D5.S0.History.Spacetime.HFMemberOccurrences.equationEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨equationArena⟩
  objectArena := .source ⟨equationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source equationArena ⟨equationEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize hfSignature (fun _ _ z => mass z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.History.Spacetime.HFMemberOccurrences
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def cardinalityRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.History.Spacetime.HFMemberOccurrences.occurrence_card)
    (type_of% (realize hfSignature (fun _ _ z => mass z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S0.History.Spacetime.HFMemberOccurrences.cardinalityUnit
  realizationName := `Reg.D5.S0.History.Spacetime.HFMemberOccurrences.cardinalityEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨cardinalityArena⟩
  objectArena := .source ⟨cardinalityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cardinalityArena ⟨cardinalityEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize hfSignature (fun _ _ z => mass z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.History.Spacetime.HFMemberOccurrences
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def naturalRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.History.Spacetime.HFMemberOccurrences.mass_natCode)
    (type_of% (realize naturalSignature (fun _ _ z => mass z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S0.History.Spacetime.HFMemberOccurrences.naturalUnit
  realizationName := `Reg.D5.S0.History.Spacetime.HFMemberOccurrences.naturalEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨naturalArena⟩
  objectArena := .source ⟨naturalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source naturalArena ⟨naturalEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize naturalSignature (fun _ _ z => mass z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.History.Spacetime.HFMemberOccurrences
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def archiveRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.History.Spacetime.HFMemberOccurrences.richCode_leaf_bound)
    (type_of% (realize archiveSignature (fun b _ z => if b then Nat.card (Occurrence z) else mass z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S0.History.Spacetime.HFMemberOccurrences.archiveUnit
  realizationName := `Reg.D5.S0.History.Spacetime.HFMemberOccurrences.archiveEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨archiveArena⟩
  objectArena := .source ⟨archiveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source archiveArena ⟨archiveEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize archiveSignature (fun b _ z => if b then Nat.card (Occurrence z) else mass z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.History.Spacetime.HFMemberOccurrences
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[
      { path := #["body", "body", "body", "body", "arg", "arg"],
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg", "arg"], booleanPredicate := false },
      { path := #["body", "body", "body", "body", "fn", "arg", "arg"],
        stateBinder := 0, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms equationEvidence
#print axioms cardinalityEvidence
#print axioms naturalEvidence
#print axioms archiveEvidence

end
end Reg.D5.S0.History.Spacetime.HFMemberOccurrences
