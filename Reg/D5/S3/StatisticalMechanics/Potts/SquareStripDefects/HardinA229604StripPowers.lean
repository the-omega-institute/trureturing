
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option maxRecDepth 100000

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace Steps
/- signature: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 24) (fun _ => Fin 96) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=typed registration evidence -/
def readout : Realization signature := realize signature (fun _ k s => W k.succ s) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=typed registration evidence -/
def rejected : Realization signature := realize signature (fun _ k s => W k.succ s + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev arena : Arena where
  signature := signature
  Law ρ := W 0 = initial ∧ ∀ (i : Fin 24) (s : Fin 96), ρ.readout () i s = Matrix.vecMul (W i.castSucc) T s
/- rejected_law: proof_shape=bind-only; consumers=typed registration evidence -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2 0 0
  have ha := steps.2 0 0
  change W 1 0 + 1 = _ at hb
  change W 1 0 = _ at ha
  linarith
/- family: proof_shape=bind-only; consumers=typed registration evidence -/
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
/- audit: proof_shape=bind-only; consumers=typed registration evidence -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@steps) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229604StripPowersSteps.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
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
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace Relation
/- signature: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 96) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=typed registration evidence -/
def readout : Realization signature := realize signature (fun _ _ s => W 24 s) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=typed registration evidence -/
def rejected : Realization signature := realize signature (fun _ _ s => W 24 s + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ s : Fin 96, ρ.readout () () s = ∑ j : Fin 21, (![137388096, -1718948736, 9979813584, -35729023024, 88409012652, -160604595216, 222060410955, -239066083215, 203308881255, -137758028106, 74677395474, -32398609896, 11214272853, -3076398702, 661896144, -110021385, 13836015, -1278486, 83214, -3573, 90] j : ℤ) * W ⟨3 + j.val, by omega⟩ s
/- rejected_law: proof_shape=bind-only; consumers=typed registration evidence -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  have ha := relation 0
  change W 24 0 + 1 = _ at hb
  change W 24 0 = _ at ha
  linarith
/- family: proof_shape=bind-only; consumers=typed registration evidence -/
def family : Registration arena (type_of% @relation) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨relation, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change W 24 0 ≠ W 24 1
    decide +kernel
/- audit: proof_shape=bind-only; consumers=typed registration evidence -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@relation) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229604StripPowersRelation.auditUnit
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
  readout := some (realize signature (fun _ _ s => W 24 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
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
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace InitialRelation
/- signature: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 21) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=typed registration evidence -/
def readout : Realization signature := realize signature (fun _ _ j => dotProduct (W ⟨2 + j.val, by omega⟩) terminal) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=typed registration evidence -/
def rejected : Realization signature := realize signature (fun _ _ j => dotProduct (W ⟨2 + j.val, by omega⟩) terminal + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev arena : Arena where
  signature := signature
  Law ρ := dotProduct (W 23) terminal = ∑ j : Fin 21, (![137388096, -1718948736, 9979813584, -35729023024, 88409012652, -160604595216, 222060410955, -239066083215, 203308881255, -137758028106, 74677395474, -32398609896, 11214272853, -3076398702, 661896144, -110021385, 13836015, -1278486, 83214, -3573, 90] j : ℤ) * ρ.readout () () j
/- rejected_law: proof_shape=bind-only; consumers=typed registration evidence -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h
  have ha := initial_relation
  change dotProduct (W 23) terminal = ∑ j : Fin 21,
    (![137388096, -1718948736, 9979813584, -35729023024, 88409012652, -160604595216, 222060410955, -239066083215, 203308881255, -137758028106, 74677395474, -32398609896, 11214272853, -3076398702, 661896144, -110021385, 13836015, -1278486, 83214, -3573, 90] j : ℤ) * (dotProduct (W ⟨2 + j.val, by omega⟩) terminal + 1) at hb
  simp only [mul_add, Finset.sum_add_distrib, mul_one] at hb
  have hc : (∑ j : Fin 21, (![137388096, -1718948736, 9979813584, -35729023024, 88409012652, -160604595216, 222060410955, -239066083215, 203308881255, -137758028106, 74677395474, -32398609896, 11214272853, -3076398702, 661896144, -110021385, 13836015, -1278486, 83214, -3573, 90] j : ℤ)) = -7 := by decide +kernel
  rw [hc] at hb
  linarith
/- family: proof_shape=bind-only; consumers=typed registration evidence -/
def family : Registration arena (type_of% @initial_relation) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨initial_relation, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    decide +kernel +revert
/- audit: proof_shape=bind-only; consumers=typed registration evidence -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@initial_relation) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229604StripPowersInitialRelation.auditUnit
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
  readout := some (realize signature (fun _ _ j => dotProduct (W ⟨2 + j.val, by omega⟩) terminal) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end InitialRelation
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
