import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTwoInjectionGroup1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTables
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTwoInjectionGroup1
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTables
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTwoInjectionGroup1

noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 19) (fun _ => Fin 41 → ℤ)
def readout : Realization signature := realize signature (fun _ _ k => SQ k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ k => SQ k + Pi.single 0 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ k : Fin 3, S.mulVec (W ⟨3+k.val, by omega⟩) = A.readout () () (⟨3+k.val, by omega⟩ : Fin 19)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) 0
  have ha := congrFun (rows 0) 0
  change S.mulVec (W 3) 0 = SQ 3 0 at ha
  change S.mulVec (W 3) 0 = SQ 3 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @rows) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨rows, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 3, 4, ?_⟩
    intro he
    have hh := congrFun he 0
    exact (by decide +kernel : SQ 3 0 ≠ SQ 4 0) hh
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@rows) (Realization signature) Type Unit where
  unitName := `Reg.A229698HardinA229698StripTwoInjectionGroup1.auditUnit
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
  readout := some (realize signature (fun _ _ k => SQ k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTwoInjectionGroup1
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTwoInjectionGroup1
