import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks.HardinA229585StripForward1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option profiler true

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks.HardinA229585StripForward1
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks.HardinA229585StripForward1
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
attribute [local irreducible] W T
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 11) (fun _ => Fin 72 → ℤ)
def readout : Realization signature := realize signature (fun _ _ x => W x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ x => W x + fun _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ i : Fin 2, R.readout () () ⟨2 + i.val + 1, by omega⟩ =
    Matrix.vecMul (W ⟨2 + i.val, by omega⟩) T
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) 0
  have ha := congrFun (forward_steps 0) 0
  change W ⟨2+0+1, by omega⟩ 0 + 1 = _ at hb
  have he : W 3 0 + 1 = W 3 0 := hb.trans ha.symm
  omega
def family : Registration arena (type_of% @forward_steps) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨forward_steps, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 3, 4, ?_⟩
    change W 3 ≠ W 4
    intro h
    have h0 := congrFun h 0
    revert h0
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@forward_steps) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks.HardinA229585StripForward1.auditUnit
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
  readout := some (realize signature (fun _ _ x => W x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks.HardinA229585StripForward1
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks.HardinA229585StripForward1
