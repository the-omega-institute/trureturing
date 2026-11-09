import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity

/-! The attainment readout retains every parameter of the original theorem telescopes. -/

namespace Reg.D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity

open _root_.D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u_1 u_2 u_3 u_4

/-- Source parameters retain both full injections. The observed state is the source relation. -/
abbrev Params := Σ A : Type u_1, Σ B : Type u_2, Σ L : Type u_3, Σ R : Type u_4,
  Σ _ : A ↪ L, B ↪ R

abbrev signature : Signature where
  Params := Params.{u_1,u_2,u_3,u_4}
  State p := SetRel p.1 p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := SetRel p.2.2.1 p.2.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1,u_2,u_3,u_4} := realize signature
  (fun _ p E => transport E p.2.2.2.2.1 p.2.2.2.2.2) (fun e => nomatch e)

def enlarged : Realization signature.{u_1,u_2,u_3,u_4} := realize signature
  (fun _ _ _ => Set.univ) (fun e => nomatch e)

abbrev leftArena : Arena where
  signature := signature.{u_1,u_2,u_3,u_4}
  Law obs := ∀
    {A : Type u_1} {B : Type u_2} {L : Type u_3} {R : Type u_4}
    (E : SetRel A B) (left : A ↪ L) (right : B ↪ R)
    (D : SetRel L R) (attained : D ⊆ obs.readout () ⟨A, B, L, R, left, right⟩ E)
    (a : A) (incident : ∃ b, (a, b) ∈ E)
    (unexposed : left a ∉ D.dom) (fresh : L) (unused : fresh ∉ Set.range left),
    ∃ alternative : A ↪ L,
      alternative a = fresh ∧
      (∀ x, x ≠ a → alternative x = left x) ∧
      D ⊆ transport E alternative right ∧
      transport E alternative right ≠ transport E left right

abbrev rightArena : Arena where
  signature := signature.{u_1,u_2,u_3,u_4}
  Law obs := ∀
    {A : Type u_1} {B : Type u_2} {L : Type u_3} {R : Type u_4}
    (E : SetRel A B) (left : A ↪ L) (right : B ↪ R)
    (D : SetRel L R) (attained : D ⊆ obs.readout () ⟨A, B, L, R, left, right⟩ E)
    (b : B) (incident : ∃ a, (a, b) ∈ E)
    (unexposed : right b ∉ D.cod) (fresh : R) (unused : fresh ∉ Set.range right),
    ∃ alternative : B ↪ R,
      alternative b = fresh ∧
      (∀ y, y ≠ b → alternative y = right y) ∧
      D ⊆ transport E left alternative ∧
      transport E left alternative ≠ transport E left right

abbrev supportArena : Arena where
  signature := signature.{u_1,u_2,u_3,u_4}
  Law obs := ∀
    {A : Type u_1} {B : Type u_2} {L : Type u_3} {R : Type u_4}
    [Fintype A] [Fintype B] [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (E : SetRel A B) (left : A ↪ L) (right : B ↪ R)
    (D : Finset (L × R))
    (attained : (D : SetRel L R) ⊆ obs.readout () ⟨A, B, L, R, left, right⟩ E)
    (left_incident : ∀ a, ∃ b, (a, b) ∈ E)
    (right_incident : ∀ b, ∃ a, (a, b) ∈ E)
    (left_slack : Fintype.card A < Fintype.card L)
    (right_slack : Fintype.card B < Fintype.card R)
    (constant : ∀ (other_left : A ↪ L) (other_right : B ↪ R),
      (D : SetRel L R) ⊆ transport E other_left other_right →
      transport E other_left other_right = transport E left right),
    SetRel.dom (D : SetRel L R) = Set.range left ∧
    SetRel.cod (D : SetRel L R) = Set.range right ∧
    max (Fintype.card A) (Fintype.card B) ≤ D.card ∧
    ∀ samples : List (L × R), samples.toFinset = D →
      max (Fintype.card A) (Fintype.card B) ≤ samples.length

abbrev SA := ULift.{u_1} Unit
abbrev SB := ULift.{u_2} Unit
abbrev SL := ULift.{u_3} Bool
abbrev SR := ULift.{u_4} Bool

def sampleLeft : SA.{u_1} ↪ SL.{u_3} :=
  ⟨fun _ => ⟨false⟩, fun _ _ _ => Subsingleton.elim _ _⟩
def sampleRight : SB.{u_2} ↪ SR.{u_4} :=
  ⟨fun _ => ⟨false⟩, fun _ _ _ => Subsingleton.elim _ _⟩

def sample : Params.{u_1,u_2,u_3,u_4} :=
  ⟨SA, SB, SL, SR, sampleLeft, sampleRight⟩

private theorem actual_dependence : ObservationalDependence signature.{u_1,u_2,u_3,u_4} actual := by
  intro i
  refine ⟨sample, ∅, Set.univ, ?_⟩
  intro heq
  have present : (ULift.up false, ULift.up false) ∈
      actual.readout i sample Set.univ :=
    ⟨(ULift.up (), ULift.up ()), Set.mem_univ _, rfl⟩
  rw [← heq] at present
  obtain ⟨p, hp, _⟩ := present
  exact hp

private theorem left_enlarged_fails : ¬ leftArena.{u_1,u_2,u_3,u_4}.Law enlarged := by
  intro h
  let D : SetRel SL.{u_3} SR.{u_4} := {(ULift.up true, ULift.up true)}
  obtain ⟨alternative, _, _, preserves, _⟩ := h Set.univ sampleLeft sampleRight D
    (by intro p hp; exact Set.mem_univ _) (ULift.up ()) ⟨ULift.up (), Set.mem_univ _⟩
    (by
      rintro ⟨y, hy⟩
      have eq := congrArg ULift.down (congrArg Prod.fst (Set.mem_singleton_iff.mp hy))
      change false = true at eq
      cases eq) (ULift.up true)
    (by
      rintro ⟨x, hx⟩
      have bad : false = true := congrArg ULift.down hx
      cases bad)
  obtain ⟨⟨a, b⟩, _, hp⟩ := preserves (Set.mem_singleton _)
  have impossible : false = true := congrArg ULift.down (congrArg Prod.snd hp)
  cases impossible

private theorem right_enlarged_fails : ¬ rightArena.{u_1,u_2,u_3,u_4}.Law enlarged := by
  intro h
  let D : SetRel SL.{u_3} SR.{u_4} := {(ULift.up true, ULift.up true)}
  obtain ⟨alternative, _, _, preserves, _⟩ := h Set.univ sampleLeft sampleRight D
    (by intro p hp; exact Set.mem_univ _) (ULift.up ()) ⟨ULift.up (), Set.mem_univ _⟩
    (by
      rintro ⟨x, hx⟩
      have eq := congrArg ULift.down (congrArg Prod.snd (Set.mem_singleton_iff.mp hx))
      change false = true at eq
      cases eq) (ULift.up true)
    (by
      rintro ⟨x, hx⟩
      have bad : false = true := congrArg ULift.down hx
      cases bad)
  obtain ⟨⟨a, b⟩, _, hp⟩ := preserves (Set.mem_singleton _)
  have impossible : false = true := congrArg ULift.down (congrArg Prod.fst hp)
  cases impossible

private theorem support_enlarged_fails : ¬ supportArena.{u_1,u_2,u_3,u_4}.Law enlarged := by
  classical
  intro h
  have constant : ∀ (l : SA.{u_1} ↪ SL.{u_3}) (r : SB.{u_2} ↪ SR.{u_4}),
      ((Finset.univ : Finset (SL × SR)) : SetRel SL SR) ⊆ transport Set.univ l r →
      transport Set.univ l r = transport Set.univ sampleLeft sampleRight := by
    intro l r subset
    obtain ⟨⟨a, b⟩, _, hp⟩ := subset (show (ULift.up false, ULift.up false) ∈
      ((Finset.univ : Finset (SL × SR)) : SetRel SL SR) from Finset.mem_univ _)
    obtain ⟨⟨a', b'⟩, _, hq⟩ := subset (show (ULift.up true, ULift.up false) ∈
      ((Finset.univ : Finset (SL × SR)) : SetRel SL SR) from Finset.mem_univ _)
    have bad : (ULift.up false : SL) = ULift.up true :=
      (congrArg Prod.fst hp).symm.trans
        ((congrArg l (Subsingleton.elim a a')).trans (congrArg Prod.fst hq))
    cases congrArg ULift.down bad
  have result := h Set.univ sampleLeft sampleRight Finset.univ
    (by intro p hp; exact Set.mem_univ _) (fun _ => ⟨ULift.up (), Set.mem_univ _⟩)
    (fun _ => ⟨ULift.up (), Set.mem_univ _⟩) (by simp [SA, SL]) (by simp [SB, SR]) constant
  have present : ULift.up true ∈ SetRel.dom ((Finset.univ : Finset (SL × SR)) : SetRel SL SR) :=
    ⟨ULift.up false, Finset.mem_univ _⟩
  rw [result.1] at present
  obtain ⟨a, ha⟩ := present
  have bad : false = true := congrArg ULift.down ha
  cases bad

def leftFamily : Registration leftArena.{u_1,u_2,u_3,u_4}
    (type_of% (@unexposed_left_label_competitor.{u_1,u_2,u_3,u_4})) where
  actual := realize signature.{u_1,u_2,u_3,u_4} actual.readout actual.anchor
  bridge := Iff.rfl
  variation := ⟨@unexposed_left_label_competitor.{u_1,u_2,u_3,u_4}, enlarged, left_enlarged_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨enlarged, ?_, rfl, left_enlarged_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def leftRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@unexposed_left_label_competitor.{u_1,u_2,u_3,u_4})
    (Realization signature.{u_1,u_2,u_3,u_4}) (type_of% (@transport.{u_1,u_2,u_3,u_4})) Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity.leftUnit
  realizationName := `Reg.D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity.leftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨leftArena⟩
  objectArena := .source ⟨leftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source leftArena ⟨leftFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature.{u_1,u_2,u_3,u_4} actual.readout actual.anchor)
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity
    definition := none
    coordinates := #[0, 1, 2, 3, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms leftFamily
#print axioms leftRegistration

def rightFamily : Registration rightArena.{u_1,u_2,u_3,u_4}
    (type_of% (@unexposed_right_label_competitor.{u_1,u_2,u_3,u_4})) where
  actual := realize signature.{u_1,u_2,u_3,u_4} actual.readout actual.anchor
  bridge := Iff.rfl
  variation := ⟨@unexposed_right_label_competitor.{u_1,u_2,u_3,u_4}, enlarged, right_enlarged_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨enlarged, ?_, rfl, right_enlarged_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def rightRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@unexposed_right_label_competitor.{u_1,u_2,u_3,u_4})
    (Realization signature.{u_1,u_2,u_3,u_4}) (type_of% (@transport.{u_1,u_2,u_3,u_4})) Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity.rightUnit
  realizationName := `Reg.D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity.rightFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rightArena⟩
  objectArena := .source ⟨rightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rightArena ⟨rightFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature.{u_1,u_2,u_3,u_4} actual.readout actual.anchor)
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity
    definition := none
    coordinates := #[0, 1, 2, 3, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms rightFamily
#print axioms rightRegistration

def supportFamily : Registration supportArena.{u_1,u_2,u_3,u_4}
    (type_of% (@positive_certificate_support_lower_bound.{u_1,u_2,u_3,u_4})) where
  actual := realize signature.{u_1,u_2,u_3,u_4} actual.readout actual.anchor
  bridge := Iff.rfl
  variation := ⟨@positive_certificate_support_lower_bound.{u_1,u_2,u_3,u_4}, enlarged, support_enlarged_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨enlarged, ?_, rfl, support_enlarged_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def supportRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_certificate_support_lower_bound.{u_1,u_2,u_3,u_4})
    (Realization signature.{u_1,u_2,u_3,u_4}) (type_of% (@transport.{u_1,u_2,u_3,u_4})) Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity.supportUnit
  realizationName := `Reg.D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity.supportFamily
  realizationSource := none
  generated := false
  arena := .source ⟨supportArena⟩
  objectArena := .source ⟨supportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source supportArena ⟨supportFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature.{u_1,u_2,u_3,u_4} actual.readout actual.anchor)
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity
    definition := none
    coordinates := #[0, 1, 2, 3, 11, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms supportFamily
#print axioms supportRegistration

end
end Reg.D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity
