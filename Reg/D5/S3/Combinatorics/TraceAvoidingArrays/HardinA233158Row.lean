import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233158Row
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact readout laws preserve the complete telescopes of the strip identities. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233158Row
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233158Row
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000


namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (U5 n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (U5 n : ℤ) + if n = 12 then 1 else 0)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+12) = 16 * R.readout () () (n+11) - 64 * R.readout () () (n+10) + 76 * R.readout () () (n+9) + 17 * R.readout () () (n+8) - 84 * R.readout () () (n+7) + 48 * R.readout () () (n+6) - 8 * R.readout () () (n+5)
private theorem rejected_law : ¬ arena.Law rejected := by
  have obstruction (u : ℕ → ℤ)
      (hu : ∀ n, u (n+12) = 16 * u (n+11) - 64 * u (n+10) + 76 * u (n+9) + 17 * u (n+8) - 84 * u (n+7) + 48 * u (n+6) - 8 * u (n+5))
      (hb : ∀ n, (u (n+12) + if n+12 = 12 then 1 else 0) = 16 * (u (n+11) + if n+11 = 12 then 1 else 0) - 64 * (u (n+10) + if n+10 = 12 then 1 else 0) + 76 * (u (n+9) + if n+9 = 12 then 1 else 0) + 17 * (u (n+8) + if n+8 = 12 then 1 else 0) - 84 * (u (n+7) + if n+7 = 12 then 1 else 0) + 48 * (u (n+6) + if n+6 = 12 then 1 else 0) - 8 * (u (n+5) + if n+5 = 12 then 1 else 0)) : False := by
    have h0 := hu 0
    have h1 := hb 0
    norm_num at h0 h1
    linarith only [h0, h1]
  exact obstruction (fun n => (U5 n : ℤ)) result
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    have h0 : U5 0 = 1 := by decide +kernel
    have h1 : U5 1 = 243 := by decide +kernel
    change (U5 0 : ℤ) ≠ (U5 1 : ℤ)
    rw [h0, h1]
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233158Row.Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233158Row.Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (U5 n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233158Row
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Recurrence
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233158Row
