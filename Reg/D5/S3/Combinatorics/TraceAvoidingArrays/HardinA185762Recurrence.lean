import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185762Recurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The literal array count as a source-bound observation in the recurrence and generating series. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185762Recurrence

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185762Recurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => count n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => count n + (if n = 1 then 1 else 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    R.readout () () 1 = 40 ∧ R.readout () () 2 = 120 ∧ R.readout () () 3 = 368 ∧
    (∀ n : ℕ, 4 ≤ n →
      (R.readout () () n : ℤ) = (R.readout () () (n - 1) : ℤ) +
        6 * (R.readout () () (n - 2) : ℤ) + (R.readout () () (n - 3) : ℤ)) ∧
    (let X : PowerSeries ℚ := PowerSeries.X
     PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (R.readout () () n : ℚ)) =
       (8 * X * (5 + 10 * X + X ^ 2)) * (1 - X - 6 * X ^ 2 - X ^ 3)⁻¹)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad : count 1 + 1 = 40 := h.1
  have hfirst : count 1 = 40 := result.1
  have hsucc : count 1 + 1 = 41 := congrArg (· + 1) hfirst
  exact (by decide : (41 : ℕ) ≠ 40) (hsucc.symm.trans hbad)

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨(show (type_of% @result) ↔ arena.Law actual from Iff.rfl).mp result,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 1, 2, ?_⟩
    change count 1 ≠ count 2
    have hfirst : count 1 = 40 := result.1
    have hsecond : count 2 = 120 := result.2.1
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185762Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185762Recurrence.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185762Recurrence
    definition := some {
      owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185762Recurrence
      name := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185762Recurrence.claim
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
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA185762Recurrence

