import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripInjection

/-! Dependent observations of the exact five-row defect counts. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripInjection
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal (Q)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripInjection
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 18) (fun _ => Fin 41 → ℤ)
def readout : Realization signature := realize signature (fun _ _ k => RU k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ k => RU k + Pi.single 0 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ k : Fin 18,
    R.mulVec ((Q ^ k.val).mulVec (1 : Fin 41 → ℤ)) = A.readout () () k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) 0
  have ha := congrFun (injection_powers 0) 0
  change _ = RU 0 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @injection_powers) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨injection_powers, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hh := congrFun he 0
    change RU 0 0 = RU 1 0 at hh
    have hn : RU 0 0 ≠ RU 1 0 := by decide +kernel
    exact hn hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@injection_powers) (Realization signature) Type Unit where
  unitName := `Reg.A229590HardinA229590StripInjection.auditUnit
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
  readout := some (realize signature (fun _ _ k => RU k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripInjection
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
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripInjection
