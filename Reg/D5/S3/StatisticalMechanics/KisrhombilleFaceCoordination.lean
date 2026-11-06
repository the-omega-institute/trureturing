import D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The infinite coordination readout and its formal generating-function constraint. -/

namespace Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination

open _root_.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (1 - X^2)^2 * (PowerSeries.mk fun n => (R.readout () () n : ℤ)) =
    1 + 6*X + 22*X^2 + 6*X^3 + X^4

private theorem initial_values : a 0 = 1 ∧ a 1 = 6 := by
  have h0 := congrArg PowerSeries.constantCoeff result
  have h1 := congrArg (PowerSeries.coeff 1) result
  norm_num at h0
  norm_num [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_X,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, pow_two] at h1
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
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    rw [initial_values.1, initial_values.2]
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination.family
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
    owner := `D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination
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
end Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination
