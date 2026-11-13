import D5.S1.Recurrence.Parity.DiagonalIterateEven
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

open PowerSeries
open _root_.D5.S1.Recurrence.Parity.DiagonalIterateEven
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.Parity.DiagonalIterateEven
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => coeff n generatingSeries) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 1 ≤ n → (Odd (r.readout () () n) ↔ ∃ k : ℕ, n = 2 ^ k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 1 (by decide)).mpr ⟨0, rfl⟩
  exact (not_odd_zero : ¬ Odd (0 : ℤ)) he

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change coeff 0 generatingSeries ≠ coeff 1 generatingSeries
    rw [coeff_zero_eq_constantCoeff, generating_equation.1, generating_equation.2.1]
    exact zero_ne_one

def result_audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Parity.DiagonalIterateEven.resultUnit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DiagonalIterateEven.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => coeff n generatingSeries)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DiagonalIterateEven
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "fn", "arg", "arg"],
        stateBinder := 0, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms result_audit

end
end Reg.D5.S1.Recurrence.Parity.DiagonalIterateEven
