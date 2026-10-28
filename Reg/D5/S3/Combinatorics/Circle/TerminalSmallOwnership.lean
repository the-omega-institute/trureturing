import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.TerminalSmallOwnership
import Reg.Support.DependentFamily

/-! A finite two-state dependent-family registration attempt for the proved
prefix. The source theorem remains the actual law; no concrete H1--H12
minimum instance or raw occurrence binding is manufactured here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.TerminalSmallOwnership

namespace Reg.D5.S3.Combinatorics.Circle.TerminalSmallOwnership

abbrev sourceScope :=
  type_of% (@actualSource_terminal_small_ownership_prefix)

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop × Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => (sourceScope, b)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ b => (False, b)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (R.readout () () true).1

theorem bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h

def source_registration : Registration arena sourceScope where
  actual := actual
  bridge := bridge
  variation := ⟨@actualSource_terminal_small_ownership_prefix, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), false, true, ?_⟩
    intro h
    have hb := congrArg Prod.snd h
    simp [actual, realize] at hb

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@actualSource_terminal_small_ownership_prefix)
    (Realization signature) Bool Unit where
  unitName :=
    `D5.S3.Combinatorics.Circle.TerminalSmallOwnership.actualSource_terminal_small_ownership_prefix.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Circle.TerminalSmallOwnership.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => (sourceScope, b)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some false
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms audit

end Reg.D5.S3.Combinatorics.Circle.TerminalSmallOwnership
