import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.BalaTrinomialCoefficientIdentity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Recurrence.BalaTrinomialCoefficientIdentity
open _root_.D5.S1.Recurrence.BalaTrinomialCoefficientIdentity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ n => coeff n (source n)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () n =
    (∑ k ∈ Finset.range (n / 2 + 1), (3*n).choose k * (n-k).choose k : ℕ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 0
  norm_num [rejected, realize] at hz

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change coeff 0 (source 0) ≠ coeff 2 (source 2)
    rw [result, result]
    norm_num [Finset.sum_range_succ, Nat.choose]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Recurrence.BalaTrinomialCoefficientIdentity.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.BalaTrinomialCoefficientIdentity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => coeff n (source n)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.BalaTrinomialCoefficientIdentity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Recurrence.BalaTrinomialCoefficientIdentity
