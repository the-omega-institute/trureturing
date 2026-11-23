import D5.S3.ConceptDynamics.PartialIdentification.RelativePastWordRecovery
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ConceptDynamics.PartialIdentification.RelativePastWordRecovery

open _root_.D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
open _root_.D5.S3.ConceptDynamics.PartialIdentification.RelativePastWordRecovery
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v

/-- The full source parameters, including the arbitrary preload and independent label universe. -/
structure Params where
  E : Type u
  order : PartialOrder E
  A : Type v
  I : Set E
  label : E → A

attribute [instance] Params.order

abbrev signature : Signature where
  Params := Params.{u, v}
  State p := {l : List p.E // ∃ J : Set p.E, Exec p.I l J}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List p.A
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} := realize signature
  (fun _ p l => l.val.map p.label) (fun e => nomatch e)

def rejected : Realization signature.{u, v} := realize signature
  (fun _ _ _ => []) (fun e => nomatch e)

/-- The complete original telescope, with only the actual word readout varied. -/
abbrev arena : Arena where
  signature := signature.{u, v}
  Law obs := ∀ {E : Type u} [order : PartialOrder E] {A : Type v}
    (I : Set E) (label : E → A),
    Function.Injective (fun l : {l : List E // ∃ J : Set E, Exec I l J} =>
      obs.readout () ⟨E, order, A, I, label⟩ l) ↔
      ∀ a b : E, a ∉ I → b ∉ I →
        (Set.Iio a \ I).Finite → (Set.Iio b \ I).Finite →
        label a = label b → a ≤ b ∨ b ≤ a

def bridge : (type_of% (@result.{u, v})) ↔ arena.{u, v}.Law actual := Iff.rfl

private def discreteOrder (T : Type u) : PartialOrder T where
  le := Eq
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

private def witness : Params.{u, v} where
  E := ULift.{u} Nat
  order := discreteOrder _
  A := ULift.{v} Nat
  I := ∅
  label x := ⟨x.down⟩

private def emptyWord : signature.{u, v}.State witness := ⟨[], witness.I, rfl⟩

private def oneWord : signature.{u, v}.State witness := by
  refine ⟨[⟨0⟩], insert ⟨0⟩ witness.I, ⟨?_, rfl⟩⟩
  refine ⟨by simp [witness], ?_⟩
  intro d hd
  change d = ⟨0⟩ ∧ ¬ (⟨0⟩ : ULift.{u} Nat) = d at hd
  exact (hd.2 hd.1.symm).elim

private theorem rejected_fails : ¬ arena.{u, v}.Law rejected := by
  intro h
  have hc : ∀ a b : witness.{u, v}.E, a ∉ witness.I → b ∉ witness.I →
      (Set.Iio a \ witness.I).Finite → (Set.Iio b \ witness.I).Finite →
      witness.label a = witness.label b → a ≤ b ∨ b ≤ a := by
    intro a b _ _ _ _ hab
    left
    change a = b
    exact congrArg (fun z : ULift.{v} Nat => (ULift.up z.down : ULift.{u} Nat)) hab
  have hi := (@h witness.E witness.order witness.A witness.I witness.label).mpr hc
  have heq := hi (a₁ := emptyWord) (a₂ := oneWord) (by rfl)
  have hnil : ([] : List witness.E) = [⟨0⟩] := congrArg Subtype.val heq
  exact List.noConfusion hnil

private theorem actual_dependence :
    ObservationalDependence signature.{u, v} actual := by
  intro i
  refine ⟨witness, emptyWord, oneWord, ?_⟩
  change ([] : List (ULift.{v} Nat)) ≠ [⟨0⟩]
  exact List.noConfusion

def family : Registration arena.{u, v} (type_of% (@result.{u, v})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@result.{u, v}), rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration (@result.{u, v})
    (Realization signature.{u, v}) (type_of% (@Exec.{u})) Unit := {
  unitName := `D5.S3.ConceptDynamics.PartialIdentification.RelativePastWordRecovery.result.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.PartialIdentification.RelativePastWordRecovery.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p l => l.val.map p.label) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@Exec.{u})
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.PartialIdentification.RelativePastWordRecovery
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "body"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.ConceptDynamics.PartialIdentification.RelativePastWordRecovery
