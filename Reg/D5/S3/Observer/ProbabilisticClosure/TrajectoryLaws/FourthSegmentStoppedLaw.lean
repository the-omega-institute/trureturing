import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
noncomputable section

abbrev wordSignature : Signature where
  Params := unitInterval
  State _ := List Letter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def wordActual : Realization wordSignature :=
  realize wordSignature (fun _ r w => wordMass r w) (fun e => nomatch e)

def wordRejected : Realization wordSignature :=
  realize wordSignature (fun _ _ _ => 0) (fun e => nomatch e)

def wordArena : Arena where
  signature := wordSignature
  Law f := ∀ (r : unitInterval) (j : ℕ) (b : Letter),
    f.readout () r (pWord j b) =
      (if b = 0 then alphaMass r else betaMass r ^ 2) * (alphaMass r * betaMass r)^j

theorem word_source_bridge : (type_of% (@p_word_mass)) ↔ wordArena.Law wordActual := Iff.rfl

theorem word_rejected : ¬ wordArena.Law wordRejected := by
  intro h
  have hh := h 1 0 0
  norm_num [wordRejected, realize, alphaMass, betaMass] at hh

def wordRegistration : Registration wordArena (type_of% (@p_word_mass)) where
  actual := wordActual
  bridge := word_source_bridge
  variation := ⟨p_word_mass, wordRejected, word_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨wordRejected, ?_, rfl, word_rejected⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : unitInterval), [], [1], ?_⟩
    change wordMass (1 : unitInterval) [] ≠ wordMass 1 [1]
    simpa [wordMass, bernoulliMeasure] using (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)

abbrev finiteSignature : Signature where
  Params := (_ : ActivePhase) × unitInterval
  State _ := List Letter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def finiteActual : Realization finiteSignature :=
  realize finiteSignature (fun _ p w => explicitStoppedWordLaw p.1 p.2 {some w})
    (fun e => nomatch e)

def finiteRejected : Realization finiteSignature :=
  realize finiteSignature (fun _ _ _ => 0) (fun e => nomatch e)

def finiteArena : Arena where
  signature := finiteSignature
  Law f := ∀ (s : ActivePhase) (r : unitInterval) (w : List Letter),
    f.readout () ⟨s,r⟩ w = if ∃ b, WordFamily s b w then wordMass r w else 0

theorem finite_source_bridge :
    (type_of% (@explicit_finite_mass)) ↔ finiteArena.Law finiteActual := Iff.rfl

theorem finite_rejected : ¬ finiteArena.Law finiteRejected := by
  intro h
  have hh := h .p 1 (pWord 0 0)
  have hf : ∃ b, WordFamily .p b (pWord 0 0) := ⟨0,0,rfl⟩
  rw [if_pos hf, p_word_mass] at hh
  norm_num [finiteRejected, realize, alphaMass, betaMass] at hh

def finiteRegistration : Registration finiteArena (type_of% (@explicit_finite_mass)) where
  actual := finiteActual
  bridge := finite_source_bridge
  variation := ⟨explicit_finite_mass, finiteRejected, finite_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨finiteRejected, ?_, rfl, finite_rejected⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨.p,1⟩, pWord 0 0, pWord 0 1, ?_⟩
    change explicitStoppedWordLaw .p 1 {some (pWord 0 0)} ≠
      explicitStoppedWordLaw .p 1 {some (pWord 0 1)}
    have hf : ∃ b, WordFamily .p b (pWord 0 0) := ⟨0,0,rfl⟩
    have hg : ∃ b, WordFamily .p b (pWord 0 1) := ⟨1,0,rfl⟩
    rw [explicit_finite_mass, if_pos hf, p_word_mass,
      explicit_finite_mass, if_pos hg, p_word_mass]
    norm_num [alphaMass, betaMass]


noncomputable def word_registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@p_word_mass) (Realization wordSignature) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.word_registration_1.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.wordRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨wordArena⟩
  objectArena := .source ⟨wordArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source wordArena ⟨wordRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize wordSignature (fun _ r w => wordMass r w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def finite_registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@explicit_finite_mass) (Realization finiteSignature) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.finite_registration_1.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.finiteRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨finiteArena⟩
  objectArena := .source ⟨finiteArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finiteArena ⟨finiteRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finiteSignature (fun _ p w => explicitStoppedWordLaw p.1 p.2 {some w}) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms wordRegistration
#print axioms word_registration_1
#print axioms finite_registration_1
#print axioms finiteRegistration

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
