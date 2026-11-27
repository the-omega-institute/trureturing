import D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233141
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound readout of the complete rational generating function. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233141

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233141
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

private def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (PowerSeries.mk fun n => (R.readout () () n : ℚ)) =
      X * (2 - 34 * X + 93 * X ^ 2 - 22 * X ^ 3 + X ^ 4) *
        ((1 - X) * (1 - 18 * X + X ^ 2) * (1 - 6 * X + X ^ 2))⁻¹

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrArg (PowerSeries.constantCoeff (R := ℚ)) h
  change constantCoeff (PowerSeries.mk fun _ => (1 : ℚ)) =
    constantCoeff (X * (2 - 34 * X + 93 * X ^ 2 - 22 * X ^ 3 + X ^ 4) *
      ((1 - X) * (1 - 18 * X + X ^ 2) * (1 - 6 * X + X ^ 2))⁻¹ :
        PowerSeries ℚ) at hb
  simpa using hb

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233141.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233141.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233141
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233141
