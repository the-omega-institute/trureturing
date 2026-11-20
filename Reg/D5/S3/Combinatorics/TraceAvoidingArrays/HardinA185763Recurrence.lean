import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185763Recurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The literal array count as a source-bound observation in the recurrence and generating series. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185763Recurrence

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185763Recurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => count n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => count n + (if n = 7 then 1 else 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    R.readout () () 1 = 104 ∧ R.readout () () 2 = 368 ∧ R.readout () () 3 = 1408 ∧
    R.readout () () 4 = 5272 ∧ R.readout () () 5 = 19992 ∧ R.readout () () 6 = 75192 ∧
    (∀ n : ℕ, 7 ≤ n →
      (R.readout () () n : ℤ) = (R.readout () () (n - 1) : ℤ) +
        10 * (R.readout () () (n - 2) : ℤ) + 3 * (R.readout () () (n - 3) : ℤ) -
        5 * (R.readout () () (n - 4) : ℤ) + (R.readout () () (n - 5) : ℤ)) ∧
    (let X : PowerSeries ℚ := PowerSeries.X
     PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (R.readout () () n : ℚ)) =
       (8 * X * (13 + 33 * X - 16 * X ^ 3 + 7 * X ^ 4 - X ^ 5)) *
         (1 - X - 10 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - X ^ 5)⁻¹)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hactual := (show arena.Law actual from result).2.2.2.2.2.2.1 7 (by decide)
  have hrejected := h.2.2.2.2.2.2.1 7 (by decide)
  change (count 7 : ℤ) =
    (count 6 : ℤ) + 10 * (count 5 : ℤ) + 3 * (count 4 : ℤ) -
      5 * (count 3 : ℤ) + (count 2 : ℤ) at hactual
  change ((count 7 + 1 : ℕ) : ℤ) =
    (count 6 : ℤ) + 10 * (count 5 : ℤ) + 3 * (count 4 : ℤ) -
      5 * (count 3 : ℤ) + (count 2 : ℤ) at hrejected
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
    have hfirst : count 1 = 104 := result.1
    have hsecond : count 2 = 368 := result.2.1
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185763Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185763Recurrence.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185763Recurrence
    definition := some {
      owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185763Recurrence
      name := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185763Recurrence.claim
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
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185763Recurrence
