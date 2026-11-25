import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.WeightedTailBudgetReduction
import Reg.D5.S3.Weil.Mertens.WeightedTailInverse

/-! Observe the ordinary tail in the terminal payment of the weighted budget. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real Set MeasureTheory LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.WeightedTailTransport (tail weightedTail)
open _root_.D5.S3.Weil.Mertens.WeightedTailInverse (a)
open _root_.D5.S3.Weil.Mertens.WeightedTailWindowMass (weightedNegativeMass)
open _root_.D5.S3.Weil.Mertens.WeightedTailBudgetReduction (budget_bounds reducedDensityTail)
open _root_.Reg.D5.S3.Weil.Mertens.WeightedTailInverse (signature actual inverseEvidence)
open private densityTail from D5.S3.Weil.Mertens.WeightedTailBudgetReduction

namespace Reg.D5.S3.Weil.Mertens.WeightedTailBudgetReduction

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {k : ℝ → ℝ} {Y B C κ : ℝ}
    (_ : 2 ≤ Y) (_ : Y ≤ B) (_ : B ≤ C) (_ : 0 < κ) (_ : κ ≤ 1 / 2)
    (_ : IntegrableOn k (Ioi Y))
    (_ : ∀ t ∈ Icc Y C, max (-tail k t) 0 ≤ t ^ (κ - 1 / 2)),
    let W := weightedNegativeMass k Y B +
      sqrt Y * max (-(R.readout () () k B - a B * weightedTail k B)) 0
    let Wred :=
      (∫ t in Y..B, max (a t * reducedDensityTail k C t - max (tail k t) 0) 0 / sqrt t) +
        sqrt Y * max (-(a B * reducedDensityTail k C B)) 0
    let M := (B ^ κ - Y ^ κ) / κ
    Wred - M ≤ W ∧ W ≤ Wred + M + sqrt Y * B ^ (κ - 1 / 2)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hneg : ∀ t ∈ Icc (2 : ℝ) 2, max (-tail (fun _ => 0) t) 0 ≤ t ^ ((1 / 2 : ℝ) - 1 / 2) :=
    fun t _ => by simp [tail]
  have hbound := (h (k := fun _ => 0) (Y := 2) (B := 2) (C := 2) (κ := 1 / 2)
    le_rfl le_rfl le_rfl (by norm_num) le_rfl (by simp) hneg).2
  norm_num [weightedNegativeMass, tail, weightedTail, reducedDensityTail, densityTail,
    rejected, realize] at hbound

def evidence : Registration arena (type_of% @budget_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨budget_bounds, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := inverseEvidence.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@budget_bounds) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.WeightedTailBudgetReduction.budget_bounds.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.WeightedTailBudgetReduction.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => tail k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.WeightedTailBudgetReduction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "value", "arg", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Weil.Mertens.WeightedTailBudgetReduction
end
