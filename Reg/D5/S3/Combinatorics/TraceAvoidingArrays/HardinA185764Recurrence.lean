import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185764Recurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The literal array count as a source-bound observation in the recurrence and generating series. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185764Recurrence

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185764Recurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => count n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => count n + (if n = 10 then 1 else 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    R.readout () () 1 = 264 ∧ R.readout () () 2 = 1128 ∧ R.readout () () 3 = 5272 ∧
    R.readout () () 4 = 24832 ∧ R.readout () () 5 = 118248 ∧ R.readout () () 6 = 562800 ∧
    R.readout () () 7 = 2680000 ∧ R.readout () () 8 = 12760448 ∧ R.readout () () 9 = 60758008 ∧
    (∀ n : ℕ, 10 ≤ n →
      (R.readout () () n : ℤ) = (R.readout () () (n - 1) : ℤ) +
        17 * (R.readout () () (n - 2) : ℤ) + 9 * (R.readout () () (n - 3) : ℤ) -
        22 * (R.readout () () (n - 4) : ℤ) - (R.readout () () (n - 5) : ℤ) +
        (R.readout () () (n - 6) : ℤ) - 6 * (R.readout () () (n - 7) : ℤ)) ∧
    (let X : PowerSeries ℚ := PowerSeries.X
     PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (R.readout () () n : ℚ)) =
       (8 * X * (33 + 108 * X - 43 * X ^ 2 - 249 * X ^ 3 - 69 * X ^ 4 +
         5 * X ^ 5 + 43 * X ^ 6 + 81 * X ^ 7 + 18 * X ^ 8)) *
         (1 - X - 17 * X ^ 2 - 9 * X ^ 3 + 22 * X ^ 4 + X ^ 5 - X ^ 6 + 6 * X ^ 7)⁻¹)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hactual := (show arena.Law actual from result).2.2.2.2.2.2.2.2.2.1 10 (by decide)
  have hrejected := h.2.2.2.2.2.2.2.2.2.1 10 (by decide)
  change (count 10 : ℤ) =
    (count 9 : ℤ) + 17 * (count 8 : ℤ) + 9 * (count 7 : ℤ) - 22 * (count 6 : ℤ) -
      (count 5 : ℤ) + (count 4 : ℤ) - 6 * (count 3 : ℤ) at hactual
  change ((count 10 + 1 : ℕ) : ℤ) =
    (count 9 : ℤ) + 17 * (count 8 : ℤ) + 9 * (count 7 : ℤ) - 22 * (count 6 : ℤ) -
      (count 5 : ℤ) + (count 4 : ℤ) - 6 * (count 3 : ℤ) at hrejected
  omega

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨(show arena.Law actual from result), rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 1, 2, ?_⟩
    change count 1 ≠ count 2
    have hfirst : count 1 = 264 := result.1
    have hsecond : count 2 = 1128 := result.2.1
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185764Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185764Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => count n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185764Recurrence
    definition := some {
      owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185764Recurrence
      name := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185764Recurrence.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185764Recurrence
