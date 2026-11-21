import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ61Subcritical
import Reg.Support.DependentFamily

/-! Dependent-family registrations for overshoot and the Pell hitting threshold. -/

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

abbrev hittingSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualWidth : Realization hittingSignature :=
  realize hittingSignature (fun _ _ c => 2 * c) (fun e => nomatch e)

def zeroWidth : Realization hittingSignature :=
  realize hittingSignature (fun _ _ _ => 0) (fun e => nomatch e)

def hittingArena : Arena where
  signature := hittingSignature
  Law r := ∀ {c : ℝ}, r.readout () () c < circumference → ∃ N, UniformForbiddenHit c N

private theorem zeroWidth_fails : ¬ hittingArena.Law zeroWidth := by
  intro h
  obtain ⟨N, hN⟩ := h (c := circumference) circumference_pos
  have hx : (0 : ℝ) ∈ Set.Icc 0 (2 * circumference) :=
    ⟨le_rfl, mul_nonneg (by norm_num) circumference_pos.le⟩
  obtain ⟨_, _, _, y, hy, _⟩ := hN 0 hx
  have hlo := hy.1
  have hhi := hy.2
  linarith only [hlo, hhi, circumference_pos]

def hittingFamily : Registration hittingArena (type_of% (@uniformForbiddenHit_pell)) where
  actual := actualWidth
  bridge := Iff.rfl
  variation := ⟨@uniformForbiddenHit_pell, zeroWidth, zeroWidth_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroWidth, ?_, rfl, zeroWidth_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    change (2 : ℝ) * 0 ≠ 2 * 1
    norm_num

def hittingRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniformForbiddenHit_pell) (Realization hittingSignature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ61Subcritical.hittingUnit
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ61Subcritical.hittingFamily
  realizationSource := none
  generated := false
  arena := .source ⟨hittingArena⟩
  objectArena := .source ⟨hittingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source hittingArena ⟨hittingFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize hittingSignature (fun _ _ c => 2 * c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ61Subcritical
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ61Subcritical
