import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185761Recurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The literal array count as a source-bound observation in the recurrence,
generating series and closed form. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185761Recurrence

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185761Recurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => count n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => count n + (if n = 3 then 1 else 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    R.readout () () 1 = 16 ∧ R.readout () () 2 = 40 ∧
    (∀ n : ℕ, 3 ≤ n →
      (R.readout () () n : ℤ) = (R.readout () () (n - 1) : ℤ) +
        4 * (R.readout () () (n - 2) : ℤ)) ∧
    (let X : PowerSeries ℚ := PowerSeries.X
     PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (R.readout () () n : ℚ)) =
       (8 * X * (2 + 3 * X)) * (1 - X - 4 * X ^ 2)⁻¹) ∧
    (∀ n : ℕ, 1 ≤ n →
      (R.readout () () n : ℝ) =
        ((2 : ℝ)⁻¹ ^ n *
          ((1 - Real.sqrt 17) ^ n * (-13 + 3 * Real.sqrt 17) +
           (1 + Real.sqrt 17) ^ n * (13 + 3 * Real.sqrt 17))) / Real.sqrt 17)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hactual := (show arena.Law actual from result).2.2.1 3 (by decide)
  have hrejected := h.2.2.1 3 (by decide)
  change (count 3 : ℤ) = (count 2 : ℤ) + 4 * (count 1 : ℤ) at hactual
  change ((count 3 + 1 : ℕ) : ℤ) = (count 2 : ℤ) + 4 * (count 1 : ℤ) at hrejected
  omega

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := by
    change claim ↔ arena.Law actual
    unfold claim generatingSeries
    rfl
  variation := ⟨(show arena.Law actual from result), rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 1, 2, ?_⟩
    change count 1 ≠ count 2
    have hfirst : count 1 = 16 := result.1
    have hsecond : count 2 = 40 := result.2.1
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185761Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185761Recurrence.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185761Recurrence
    definition := some {
      owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185761Recurrence
      name := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185761Recurrence.claim
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
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185761Recurrence
