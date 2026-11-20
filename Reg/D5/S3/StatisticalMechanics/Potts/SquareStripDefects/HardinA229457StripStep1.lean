import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripStep1
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option maxRecDepth 100000

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripStep1
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripStep1
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
/- signature: proof_shape=bind-only; consumers=readout, rejected, arena, audit -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 12) (fun _ => Fin 32) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=family -/
def readout : Realization signature := realize signature (fun _ i s => W ⟨13 + i.val + 1, by omega⟩ (s.natAdd 10)) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=rejected_law, family -/
def rejected : Realization signature := realize signature (fun _ i s => W ⟨13 + i.val + 1, by omega⟩ (s.natAdd 10) + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=rejected_law, family, audit -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ (i : Fin 12) (s : Fin 32),
    ρ.readout () i s = Matrix.vecMul (W ⟨13 + i.val, by omega⟩) T (s.natAdd 10)
/- rejected_law: proof_shape=bind-only; consumers=family -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0
  have ha := steps 0 0
  change W 14 10 + 1 = _ at hb
  change W 14 10 = _ at ha
  linarith
/- family: proof_shape=bind-only; consumers=audit -/
def family : Registration arena (type_of% @steps) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨steps, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change W 14 10 ≠ W 14 11
    decide +kernel
/- audit: proof_shape=bind-only; consumers=compiled Contract.Registration inspection -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@steps) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229457StripStep1.auditUnit
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
  readout := some (realize signature (fun _ i s => W ⟨13 + i.val + 1, by omega⟩ (s.natAdd 10)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripStep1
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
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripStep1
