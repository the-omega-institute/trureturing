import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option maxRecDepth 100000

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace Steps
/- signature: proof_shape=bind-only; consumers=readout, rejected, arena, audit -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 25) (fun _ => Fin 42) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=family -/
def readout : Realization signature := realize signature (fun _ k s => W k.succ s) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=rejected_law, family -/
def rejected : Realization signature := realize signature (fun _ k s => W k.succ s + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=rejected_law, family, audit -/
abbrev arena : Arena where
  signature := signature
  Law ρ := W 0 = initial ∧ ∀ (i : Fin 25) (s : Fin 42),
    ρ.readout () i s = Matrix.vecMul (W i.castSucc) T s
/- rejected_law: proof_shape=bind-only; consumers=family -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2 0 0
  have ha := steps.2 0 0
  change W 1 0 + 1 = _ at hb
  change W 1 0 = _ at ha
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
    change W 1 0 ≠ W 1 1
    decide +kernel
/- audit: proof_shape=bind-only; consumers=compiled Contract.Registration inspection -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@steps) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229457StripPowersSteps.auditUnit
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
  readout := some (realize signature (fun _ k s => W k.succ s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Steps
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace Relation
/- signature: proof_shape=bind-only; consumers=readout, rejected, arena, audit -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 42) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=family -/
def readout : Realization signature := realize signature (fun _ _ s => W 15 s) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=rejected_law, family -/
def rejected : Realization signature := realize signature (fun _ _ s => W 15 s + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=rejected_law, family, audit -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ s : Fin 42, ρ.readout () () s =
    ∑ j : Fin 14, (![-266256, 2220864, -8262712, 18139608, -26188161, 26218062, -18693789, 9593166, -3537110, 924894, -167163, 20016, -1482, 60] j : ℤ) * W ⟨1 + j.val, by omega⟩ s
/- rejected_law: proof_shape=bind-only; consumers=family -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  have ha := relation 0
  change W 15 0 + 1 = _ at hb
  linarith
/- family: proof_shape=bind-only; consumers=audit -/
def family : Registration arena (type_of% @relation) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨relation, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change W 15 0 ≠ W 15 1
    decide +kernel
/- audit: proof_shape=bind-only; consumers=compiled Contract.Registration inspection -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@relation) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229457StripPowersRelation.auditUnit
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
  readout := some (realize signature (fun _ _ s => W 15 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Relation
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers
