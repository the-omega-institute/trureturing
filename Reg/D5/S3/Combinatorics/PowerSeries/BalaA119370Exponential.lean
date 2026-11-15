import D5.S3.Combinatorics.PowerSeries.BalaA119370Exponential
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound audit of the complete A119370 statement. -/

open PowerSeries Finset
open scoped PowerSeries.WithPiTopology
open _root_.D5.S3.Combinatorics.PowerSeries.BalaA119370Exponential
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.PowerSeries.BalaA119370Exponential
noncomputable section

private local instance : UniformSpace ℚ := ⊥

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => PowerSeries ℚ) (fun _ => PowerSeries ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ A => A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete original statement, varying its actual source-series operand. -/
abbrev arena : Arena where
  signature := signature
  Law r :=
    (∃! A : PowerSeries ℚ, IsSourceSeries A) ∧
    constantCoeff logarithm = 0 ∧
    HasSum (fun n : ℕ => C (1 / ((n + 1 : ℕ) : ℚ)) * row (n + 1) * X ^ (n + 1)) logarithm ∧
    (∀ m n : ℕ, m < n → coeff m (C (1 / (n : ℚ)) * row n * X ^ n) = 0) ∧
    HasSum (fun j : ℕ => C (1 / (j.factorial : ℚ)) * logarithm ^ j) (formalExp logarithm) ∧
    (∀ m j : ℕ, m < j → coeff m (logarithm ^ j) = 0) ∧
    (∀ m : ℕ, coeff m (formalExp logarithm) =
      ∑ j ∈ range (m + 1), (1 / (j.factorial : ℚ)) * coeff m (logarithm ^ j)) ∧
    ∀ A : PowerSeries ℚ, IsSourceSeries A →
      r.readout () () A = 1 + X * formalExp logarithm ∧
      (∀ m : ℕ, coeff m A = coeff m (1 + X * formalExp logarithm)) ∧
      (∃! S : PowerSeries ℚ, constantCoeff S = 1 ∧ S ^ 2 = discriminant) ∧
      ∀ S : PowerSeries ℚ, constantCoeff S = 1 → S ^ 2 = discriminant →
        X ∣ (1 + X ^ 2) - S ∧ A = printedBranch S

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, hA, _⟩ := result.1
  have he := (h.2.2.2.2.2.2.2 A hA).1
  have hz := congrArg constantCoeff he
  simp [rejected, realize] at hz

/-- Kernel-checked whole-statement bridge, intervention, sensitivity and dependence. -/
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : PowerSeries ℚ) ≠ 1
    exact zero_ne_one

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PowerSeries.BalaA119370Exponential.resultUnit
  realizationName := `Reg.D5.S3.Combinatorics.PowerSeries.BalaA119370Exponential.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PowerSeries.BalaA119370Exponential
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.PowerSeries.BalaA119370Exponential
