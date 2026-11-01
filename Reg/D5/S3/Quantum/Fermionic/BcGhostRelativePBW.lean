import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostRelativePBW

/-! Escape registration for the actual relative ghost PBW carrier and mode interface. -/

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostRelativePBW

open _root_.D5.S3.Quantum.Fermionic.BcGhostRelativePBW
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ => relative_pbw_complete) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () ()

def rejected : Realization signature := realize signature
  (fun _ _ => False) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h

def family : Registration arena (type_of% @relative_pbw_complete) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨relative_pbw_complete, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨(), (), ?_⟩
    exact relative_pbw_complete

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@relative_pbw_complete) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostRelativePBW.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostRelativePBW.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => relative_pbw_complete) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Unit
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostRelativePBW
    definition := none
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Fermionic.BcGhostRelativePBW
