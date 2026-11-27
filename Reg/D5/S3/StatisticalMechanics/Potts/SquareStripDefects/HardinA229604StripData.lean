import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
set_option maxRecDepth 100000

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace LeadingBlock
/- signature: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 42) (fun _ => Fin 42) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=typed registration evidence -/
def readout : Realization signature := realize signature (fun _ i j => T (i.castAdd 54) (j.castAdd 54)) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=typed registration evidence -/
def rejected : Realization signature := realize signature (fun _ i j => T (i.castAdd 54) (j.castAdd 54) + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ (i j : Fin 42), ρ.readout () i j = _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData.T i j
/- rejected_law: proof_shape=bind-only; consumers=typed registration evidence -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0
  have ha := leading_block 0 0
  change T ((0 : Fin 42).castAdd 54) ((0 : Fin 42).castAdd 54) + 1 = _ at hb
  change T ((0 : Fin 42).castAdd 54) ((0 : Fin 42).castAdd 54) = _ at ha
  linarith
/- family: proof_shape=bind-only; consumers=typed registration evidence -/
def family : Registration arena (type_of% @leading_block) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨leading_block, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T ((0 : Fin 42).castAdd 54) ((0 : Fin 42).castAdd 54) ≠ T ((0 : Fin 42).castAdd 54) ((1 : Fin 42).castAdd 54)
    decide +kernel
/- audit: proof_shape=bind-only; consumers=typed registration evidence -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@leading_block) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229604StripDataLeadingBlock.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ i j => T (i.castAdd 54) (j.castAdd 54)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end LeadingBlock
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace TerminalBlock
/- signature: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 32) (fun _ => Fin 32) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=typed registration evidence -/
def readout : Realization signature := realize signature (fun _ i j => T ((i.natAdd 42).castAdd 22) ((j.natAdd 42).castAdd 22)) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=typed registration evidence -/
def rejected : Realization signature := realize signature (fun _ i j => T ((i.natAdd 42).castAdd 22) ((j.natAdd 42).castAdd 22) + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ (i j : Fin 32), ρ.readout () i j = _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData.T (i.natAdd 10) (j.natAdd 10)
/- rejected_law: proof_shape=bind-only; consumers=typed registration evidence -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0
  have ha := terminal_block 0 0
  change T (((0 : Fin 32).natAdd 42).castAdd 22) (((0 : Fin 32).natAdd 42).castAdd 22) + 1 = _ at hb
  change T (((0 : Fin 32).natAdd 42).castAdd 22) (((0 : Fin 32).natAdd 42).castAdd 22) = _ at ha
  linarith
/- family: proof_shape=bind-only; consumers=typed registration evidence -/
def family : Registration arena (type_of% @terminal_block) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨terminal_block, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T (((0 : Fin 32).natAdd 42).castAdd 22) (((0 : Fin 32).natAdd 42).castAdd 22) ≠ T (((0 : Fin 32).natAdd 42).castAdd 22) (((1 : Fin 32).natAdd 42).castAdd 22)
    decide +kernel
/- audit: proof_shape=bind-only; consumers=typed registration evidence -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@terminal_block) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229604StripDataTerminalBlock.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ i j => T ((i.natAdd 42).castAdd 22) ((j.natAdd 42).castAdd 22)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end TerminalBlock
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
