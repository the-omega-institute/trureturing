import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Words.AdmissibleWords.UncrossingFiber

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.GenericEnergy

open _root_.D5.S1.Words.AdmissibleWords.UncrossingFiber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- Original arbitrary V : Type is the sole coordinate. Dictionaries stay in Law. -/
abbrev signature : Signature.{1, 0, 0, 0, 0} where
  Params := Type
  State V := Multiset (Finset V)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Saved matching compiler material gives energy : {V : Type} → Multiset (Finset V) → Nat. -/
def actual : Realization signature := realize signature
  (fun _ V M => @energy V M) (fun e => nomatch e)

def badZero : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

def badOne : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨Fin 1, (0 : Multiset (Finset (Fin 1))),
    ({(0 : Fin 1)} : Finset (Fin 1)) ::ₘ 0, ?_⟩
  change energy (0 : Multiset (Finset (Fin 1))) ≠
    energy (({(0 : Fin 1)} : Finset (Fin 1)) ::ₘ 0)
  simp [energy, height]

/-- Higher-universe singleton-role proof; the Type-0 support helper is not applied. -/
private theorem singleton_sensitivity
    (law : Realization signature → Prop) (bad : Realization signature)
    (hbad : ¬ law bad) : Sensitivity ⟨signature, law⟩ actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, hbad⟩
    · intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

private abbrev crossingLeft : Finset (Fin 2) := {0}
private abbrev crossingRight : Finset (Fin 2) := {1}
private abbrev crossingInput : Multiset (Finset (Fin 2)) :=
  crossingLeft ::ₘ crossingRight ::ₘ 0
private abbrev crossingOutput : Multiset (Finset (Fin 2)) :=
  (crossingLeft ∩ crossingRight) ::ₘ (crossingLeft ∪ crossingRight) ::ₘ 0

private theorem crossing_step : ForwardStep crossingInput crossingOutput := by
  refine ⟨0, crossingLeft, crossingRight, ?_, ?_, rfl, rfl⟩
  · decide
  · decide

private theorem crossing_input_energy : energy crossingInput = 2 := by
  simp [crossingInput, crossingLeft, crossingRight, energy, height]

namespace Audit_forwardStep_energy

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V] {M N : Multiset (Finset V)} (h : ForwardStep M N),
    ∃ A B R, (¬ A ⊆ B) ∧ (¬ B ⊆ A) ∧
      M = A ::ₘ B ::ₘ R ∧ N = (A ∩ B) ::ₘ (A ∪ B) ::ₘ R ∧
      F.readout () V N = energy M +
        2 * (A \ B).card * (B \ A).card

theorem actual_law : arena.Law actual := @forwardStep_energy

theorem bridge : (type_of% (@forwardStep_energy)) ↔ arena.Law actual := Iff.rfl

theorem bad_law : ¬ arena.Law badZero := by
  intro h
  obtain ⟨A, B, R, hAB, hBA, hM, hN, hE⟩ :=
    @h (Fin 2) inferInstance inferInstance crossingInput crossingOutput crossing_step
  change (0 : Nat) = energy crossingInput +
    2 * (A \ B).card * (B \ A).card at hE
  rw [crossing_input_energy] at hE
  omega

def registration : Registration arena (type_of% (@forwardStep_energy)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, badZero, bad_law⟩
  sensitivity := singleton_sensitivity _ badZero bad_law
  dependence := actual_dependence

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@forwardStep_energy)
      (type_of% (realize signature (fun _ V M => @energy V M) (fun e => nomatch e)))
      Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.forwardStep_energy.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.GenericEnergy.Audit_forwardStep_energy.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ V M => @energy V M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Audit_forwardStep_energy

namespace Audit_forwardStep_energy_gap

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V] {M N : Multiset (Finset V)} (h : ForwardStep M N),
    energy M + 2 ≤ F.readout () V N

theorem actual_law : arena.Law actual := @forwardStep_energy_gap

theorem bridge : (type_of% (@forwardStep_energy_gap)) ↔ arena.Law actual := Iff.rfl

theorem bad_law : ¬ arena.Law badZero := by
  intro h
  have hE : energy crossingInput + 2 ≤ 0 :=
    @h (Fin 2) inferInstance inferInstance crossingInput crossingOutput crossing_step
  omega

def registration : Registration arena (type_of% (@forwardStep_energy_gap)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, badZero, bad_law⟩
  sensitivity := singleton_sensitivity _ badZero bad_law
  dependence := actual_dependence

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@forwardStep_energy_gap)
      (type_of% (realize signature (fun _ V M => @energy V M) (fun e => nomatch e)))
      Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.forwardStep_energy_gap.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.GenericEnergy.Audit_forwardStep_energy_gap.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ V M => @energy V M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Audit_forwardStep_energy_gap

namespace Audit_forwardStep_energy_strict

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V] {M N : Multiset (Finset V)} (h : ForwardStep M N),
    energy M < F.readout () V N

theorem actual_law : arena.Law actual := @forwardStep_energy_strict

theorem bridge : (type_of% (@forwardStep_energy_strict)) ↔ arena.Law actual := Iff.rfl

theorem bad_law : ¬ arena.Law badZero := by
  intro h
  have hE : energy crossingInput < 0 :=
    @h (Fin 2) inferInstance inferInstance crossingInput crossingOutput crossing_step
  omega

def registration : Registration arena (type_of% (@forwardStep_energy_strict)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, badZero, bad_law⟩
  sensitivity := singleton_sensitivity _ badZero bad_law
  dependence := actual_dependence

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@forwardStep_energy_strict)
      (type_of% (realize signature (fun _ V M => @energy V M) (fun e => nomatch e)))
      Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.forwardStep_energy_strict.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.GenericEnergy.Audit_forwardStep_energy_strict.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ V M => @energy V M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Audit_forwardStep_energy_strict

namespace Audit_energy_le_card_mul_fintype_card_sq

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V] (M : Multiset (Finset V)),
    F.readout () V M ≤ M.card * (Fintype.card V) ^ 2

theorem actual_law : arena.Law actual := @energy_le_card_mul_fintype_card_sq

theorem bridge : (type_of% (@energy_le_card_mul_fintype_card_sq)) ↔ arena.Law actual := Iff.rfl

theorem bad_law : ¬ arena.Law badOne := by
  intro h
  have hE := @h (Fin 1) inferInstance inferInstance (0 : Multiset (Finset (Fin 1)))
  have impossible : (1 : Nat) ≤ 0 := by
    simpa [badOne, realize] using hE
  omega

def registration : Registration arena (type_of% (@energy_le_card_mul_fintype_card_sq)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, badOne, bad_law⟩
  sensitivity := singleton_sensitivity _ badOne bad_law
  dependence := actual_dependence

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@energy_le_card_mul_fintype_card_sq)
      (type_of% (realize signature (fun _ V M => @energy V M) (fun e => nomatch e)))
      Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.energy_le_card_mul_fintype_card_sq.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.GenericEnergy.Audit_energy_le_card_mul_fintype_card_sq.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ V M => @energy V M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Audit_energy_le_card_mul_fintype_card_sq

namespace Audit_exists_forward_route_to_comparable

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V] (M : Multiset (Finset V)),
    ∃ k N, 2 * k + F.readout () V M ≤ M.card * (Fintype.card V) ^ 2 ∧
      k ≤ M.card * (Fintype.card V) ^ 2 / 2 ∧ ForwardRoute M N k ∧ Comparable N

theorem actual_law : arena.Law actual := @exists_forward_route_to_comparable

theorem bridge : (type_of% (@exists_forward_route_to_comparable)) ↔ arena.Law actual := Iff.rfl

theorem bad_law : ¬ arena.Law badOne := by
  intro h
  obtain ⟨k, N, hE, hfloor, hroute, hcomparable⟩ :=
    @h (Fin 1) inferInstance inferInstance (0 : Multiset (Finset (Fin 1)))
  simpa [badOne, realize] using hE

def registration : Registration arena (type_of% (@exists_forward_route_to_comparable)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, badOne, bad_law⟩
  sensitivity := singleton_sensitivity _ badOne bad_law
  dependence := actual_dependence

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@exists_forward_route_to_comparable)
      (type_of% (realize signature (fun _ V M => @energy V M) (fun e => nomatch e)))
      Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.exists_forward_route_to_comparable.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.GenericEnergy.Audit_exists_forward_route_to_comparable.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ V M => @energy V M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Audit_exists_forward_route_to_comparable

namespace Audit_sort_to_threshold

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {V : Type} [Fintype V] [DecidableEq V] (M : Multiset (Finset V)),
    ∃ k, 2 * k + F.readout () V M ≤ M.card * (Fintype.card V) ^ 2 ∧
      k ≤ M.card * (Fintype.card V) ^ 2 / 2 ∧ ForwardRoute M (thresholdRows M) k

theorem actual_law : arena.Law actual := @sort_to_threshold

theorem bridge : (type_of% (@sort_to_threshold)) ↔ arena.Law actual := Iff.rfl

theorem bad_law : ¬ arena.Law badOne := by
  intro h
  obtain ⟨k, hE, hfloor, hroute⟩ :=
    @h (Fin 1) inferInstance inferInstance (0 : Multiset (Finset (Fin 1)))
  simpa [badOne, realize] using hE

def registration : Registration arena (type_of% (@sort_to_threshold)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, badOne, bad_law⟩
  sensitivity := singleton_sensitivity _ badOne bad_law
  dependence := actual_dependence

noncomputable def audit :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@sort_to_threshold)
      (type_of% (realize signature (fun _ V M => @energy V M) (fun e => nomatch e)))
      Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.UncrossingFiber.sort_to_threshold.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.GenericEnergy.Audit_sort_to_threshold.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ V M => @energy V M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Audit_sort_to_threshold

end Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.GenericEnergy
