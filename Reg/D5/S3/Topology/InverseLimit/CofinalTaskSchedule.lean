import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.CofinalTaskSchedule

/-! Source-bound reservation observations retain the complete cofinality law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Topology.InverseLimit.SignedProperLimit
open _root_.D5.S3.Topology.InverseLimit.CofinalTaskSchedule
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace Reg.D5.S3.Topology.InverseLimit.CofinalTaskSchedule

abbrev sourceScope := type_of% (@exists_reservation_above)

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Label
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Task
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ a => (reservation a).1) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ (task : Task) (base : Label), ∃ a, base < a ∧ r.readout () () a = task

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual :=
  source_bridge.mp @exists_reservation_above

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => .inl fallback) (fun e => nomatch e)

private def delayedTask : Task := .inr (fallback.1, fallback.2, fallback.2, 0)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, _, ha⟩ := h delayedTask fallback.2
  change (Sum.inl fallback : Task) = Sum.inr (fallback.1, fallback.2, fallback.2, 0) at ha
  cases ha

noncomputable def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases j
      exact (hj rfl).elim
    · intro e
      exact Empty.elim e
  dependence := by
    intro i
    cases i
    refine ⟨(), reservation.symm (.inl fallback, fallback.2),
      reservation.symm (delayedTask, fallback.2), ?_⟩
    intro he
    change (reservation (reservation.symm (.inl fallback, fallback.2))).1 =
      (reservation (reservation.symm (delayedTask, fallback.2))).1 at he
    simp only [Equiv.apply_symm_apply] at he
    change (Sum.inl fallback : Task) = Sum.inr (fallback.1, fallback.2, fallback.2, 0) at he
    cases he

/-- The readout is the exact first component of the reserved pair at the
existential stage in the original cofinality statement. -/
noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 1, 0, 1, 0, 0}
      (@exists_reservation_above) (DependentFamily.Realization signature) Unit True where
  unitName :=
    `D5.S3.Topology.InverseLimit.CofinalTaskSchedule.exists_reservation_above.__information_unit
  realizationName := `Reg.D5.S3.Topology.InverseLimit.CofinalTaskSchedule.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (DependentFamily.realize signature
    (fun _ _ a => (reservation a).1) (fun e => nomatch e))
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.InverseLimit.CofinalTaskSchedule
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- The remaining targets retain their original telescopes without a validation claim. -/
abbrev executionScope := type_of% (@execute_valid)
abbrev ordinaryScope := type_of% (@ordinary_cofinal)
abbrev delayedScope := type_of% (@delayed_cofinal)

theorem execution_source : executionScope := @execute_valid
theorem ordinary_source : ordinaryScope := @ordinary_cofinal
theorem delayed_source : delayedScope := @delayed_cofinal

end Reg.D5.S3.Topology.InverseLimit.CofinalTaskSchedule
