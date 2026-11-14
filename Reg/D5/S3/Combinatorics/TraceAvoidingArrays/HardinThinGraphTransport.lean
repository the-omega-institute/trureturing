import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ × ℕ × ℕ × ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ n =>
    (Nat.card ((stripGraph true n 1).Coloring (Fin 3)),
     Nat.card ((stripGraph false n 1).Coloring (Fin 3)),
     Nat.card ((stripGraph true n 2).Coloring (Fin 3)),
     Nat.card ((stripGraph false n 2).Coloring (Fin 3)))) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 1, 0, 0)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n, (R.readout () () n).1 = (R.readout () () n).2.1 ∧
    (R.readout () () n).2.2.1 = (R.readout () () n).2.2.2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 0).1
  change (0 : ℕ) = 1 at h0
  omega

/-- Exact positive law and full-family intervention; source binding and actual dependence are pending. -/
def variation : Variation arena actual := by
  exact ⟨result, rejected, rejected_law⟩

/-- Sensitivity of the selected complete count vector under a whole-family intervention. -/
def sensitivity : Sensitivity arena actual :=
  _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law

/-- The raw count-vector law has the full original quantifier and both widths. -/
def bridge : (type_of% @result) ↔ arena.Law actual := Iff.rfl

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
