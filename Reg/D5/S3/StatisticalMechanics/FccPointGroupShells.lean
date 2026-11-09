import D5.S3.StatisticalMechanics.FccPointGroupShells
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! A dependent readout of the shell-orbit count and its generating-function constraint. -/

namespace Reg.D5.S3.StatisticalMechanics.FccPointGroupShells

open _root_.D5.S3.StatisticalMechanics.FccPointGroupShells
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => A n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => A n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (1 - X) * (1 - X^2)^2 * (1 - X^3) *
      (PowerSeries.mk fun n => (R.readout () () n : ℤ)) = 1 - X^5

private theorem initial_values : A 0 = 1 ∧ A 2 = 3 := by
  have h0 := congrArg PowerSeries.constantCoeff result
  have h1 := congrArg (PowerSeries.coeff 1) result
  have h2 := congrArg (PowerSeries.coeff 2) result
  norm_num at h0
  norm_num [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_X,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, pow_two] at h1 h2
  omega

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrArg PowerSeries.constantCoeff h
  have ha := initial_values.1
  norm_num [rejected, realize] at hb
  omega

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change A 0 ≠ A 2
    rw [initial_values.1, initial_values.2]
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.FccPointGroupShells.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.FccPointGroupShells.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => A n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.FccPointGroupShells
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S3.StatisticalMechanics.FccPointGroupShells
