import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripStepGroup4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTables
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripStepGroup4
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTables
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripStepGroup4

noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 28) (fun _ => Fin 41 → ℤ)
def readout : Realization signature := realize signature (fun _ _ k => V k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ k => V k + Pi.single 0 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ k : Fin 5, A.readout () () (⟨20+k.val+1, by omega⟩ : Fin 28) =
    Q.mulVec (V ⟨20+k.val, by omega⟩) + J ⟨20+k.val, by omega⟩
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) 0
  have ha := congrFun (steps 0) 0
  change V 21 0 = (Q.mulVec (V 20) + J 20) 0 at ha
  change V 21 0 + 1 = (Q.mulVec (V 20) + J 20) 0 at hb
  linarith
def family : Registration arena (type_of% @steps) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨steps, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 21, 22, ?_⟩
    intro he
    have hh := congrFun he 0
    exact (by decide +kernel : V 21 0 ≠ V 22 0) hh
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@steps) (Realization signature) Type Unit where
  unitName := `Reg.A229698HardinA229698StripStepGroup4.auditUnit
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
  readout := some (realize signature (fun _ _ k => V k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripStepGroup4
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
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripStepGroup4
