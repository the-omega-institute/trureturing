import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripOneInjectionGroup0
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTables
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripOneInjectionGroup0
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTables
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripOneInjectionGroup0

noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 27) (fun _ => Fin 41 → ℤ)
def readout : Realization signature := realize signature (fun _ _ k => J k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ k => J k + Pi.single 0 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ k : Fin 4, HardinA229590StripData.R.mulVec (HardinA229590StripData.U ⟨0+k.val, by omega⟩) + SQ ⟨0+k.val, by omega⟩ = A.readout () () (⟨0+k.val, by omega⟩ : Fin 27)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) 0
  have ha := congrFun (rows 0) 0
  change (HardinA229590StripData.R.mulVec (HardinA229590StripData.U 0) + SQ 0) 0 = J 0 0 at ha
  change (HardinA229590StripData.R.mulVec (HardinA229590StripData.U 0) + SQ 0) 0 = J 0 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @rows) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨rows, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hh := congrFun he 0
    exact (by decide +kernel : J 0 0 ≠ J 1 0) hh
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@rows) (Realization signature) Type Unit where
  unitName := `Reg.A229698HardinA229698StripOneInjectionGroup0.auditUnit
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
  readout := some (realize signature (fun _ _ k => J k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripOneInjectionGroup0
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
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripOneInjectionGroup0
