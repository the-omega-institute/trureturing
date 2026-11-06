import D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The entire coordination sequence is observed at each cylinder width. -/

namespace Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination

open _root_.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => c n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n m => c n m + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n →
    (1-X)^2 * (PowerSeries.mk fun m => (R.readout () () n m : ℤ)) =
      (1-X)*(1+2*X-C ((n : ℤ)-2)*X^(2*n)-C ((n : ℤ)-1)*X^(2*n+1)) +
        3*X^2*(1-X^(2*n-2))

private theorem initial_values : c 1 0 = 1 ∧ c 1 2 = 4 ∧ c 2 2 = 6 := by
  have h₁₀ := congrArg PowerSeries.constantCoeff (result 1 (by omega))
  have h₁₁ := congrArg (PowerSeries.coeff 1) (result 1 (by omega))
  have h₁₂ := congrArg (PowerSeries.coeff 2) (result 1 (by omega))
  have h₂₀ := congrArg PowerSeries.constantCoeff (result 2 (by omega))
  have h₂₁ := congrArg (PowerSeries.coeff 1) (result 2 (by omega))
  have h₂₂ := congrArg (PowerSeries.coeff 2) (result 2 (by omega))
  norm_num at h₁₀ h₂₀
  norm_num [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_X,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, pow_two] at h₁₁ h₁₂ h₂₁ h₂₂
  omega

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrArg PowerSeries.constantCoeff (h 1 (by omega))
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
    refine ⟨(), 1, 2, ?_⟩
    change c 1 ≠ c 2
    intro h
    have he := congrFun h 2
    rw [initial_values.2.1, initial_values.2.2] at he
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => c n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
