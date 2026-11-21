import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ61Subcritical
import Reg.Support.DependentFamily

/-! Dependent-family registration of the zero-overshoot criterion. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.MeyerovitchYoungQ61Subcritical

set_option autoImplicit false

namespace Reg.D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ61Subcritical

noncomputable section

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ W y => overshoot W y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ W y : ℝ, r.readout () W y = 0 ↔ y ∈ Set.Icc 0 W

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hbad : (1 : ℝ) ∈ Set.Icc 0 0 := (h 0 1).mp rfl
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hbad.2

private theorem actual_depends_on_position : ObservationalDependence signature actual := by
  intro _
  refine ⟨0, 0, 1, ?_⟩
  change overshoot 0 0 ≠ overshoot 0 1
  have hzero := (overshoot_eq_zero_iff 0 0).mpr ⟨le_rfl, le_rfl⟩
  intro h
  have hbad : (1 : ℝ) ∈ Set.Icc 0 0 := (overshoot_eq_zero_iff 0 1).mp (h.symm.trans hzero)
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hbad.2

def overshootFamily : Registration arena (type_of% overshoot_eq_zero_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨overshoot_eq_zero_iff, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j h
      have sameRole : (j : Unit) = (i : Unit) :=
        @Subsingleton.elim Unit inferInstance j i
      exact (h sameRole).elim
    · intro e
      exact nomatch e
  dependence := actual_depends_on_position

def overshootRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    overshoot_eq_zero_iff (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ61Subcritical.overshootUnit
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ61Subcritical.overshootFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨overshootFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ W y => overshoot W y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ61Subcritical
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ61Subcritical
