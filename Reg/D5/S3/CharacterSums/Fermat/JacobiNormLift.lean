import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.Fermat.JacobiNormLift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.LanglandsFirstMainLemma

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.CharacterSums.Fermat.JacobiNormLift

noncomputable section
universe u v

abbrev claim : Prop :=
  type_of% (@_root_.D5.S3.CharacterSums.Fermat.JacobiNormLift.neg_jacobiSum_norm_lift.{u, v})

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => if b then claim.{u, v} else False) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () true

private theorem bridge :
    (type_of% (@_root_.D5.S3.CharacterSums.Fermat.JacobiNormLift.neg_jacobiSum_norm_lift.{u, v})) ↔
      arena.Law (actual.{u, v}) := by
  rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  simp [arena, rejected, realize]

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.CharacterSums.Fermat.JacobiNormLift.neg_jacobiSum_norm_lift.{u, v})) where
  actual := actual.{u, v}
  bridge := bridge
  variation := ⟨bridge.mp @_root_.D5.S3.CharacterSums.Fermat.JacobiNormLift.neg_jacobiSum_norm_lift.{u, v},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), true, false, ?_⟩
    change claim.{u, v} ≠ False
    intro h
    exact h ▸ (@_root_.D5.S3.CharacterSums.Fermat.JacobiNormLift.neg_jacobiSum_norm_lift.{u, v})

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.CharacterSums.Fermat.JacobiNormLift.neg_jacobiSum_norm_lift.{u, v})
    (Realization signature) Unit Unit where
  unitName := `D5.S3.CharacterSums.Fermat.JacobiNormLift.neg_jacobiSum_norm_lift.__information_unit
  realizationName := `Reg.D5.S3.CharacterSums.Fermat.JacobiNormLift.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => if b then claim.{u, v} else False)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.CharacterSums.Fermat.JacobiNormLift
