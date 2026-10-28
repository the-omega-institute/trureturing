import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Analytic.SeriesInequalities.ForbergExponentialFloor

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.SeriesInequalities.ForbergExponentialFloor
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.ForbergExponentialFloor

@[reducible] def signature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n =>
    ⌊(n : ℝ) / (Real.exp (4 / (n : ℝ)) - 1)⌋) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun i p n => actual.readout i p n + 1) (fun e => nomatch e)

@[reducible] def arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ (n : ℕ), 1 ≤ n → R.readout () () n = ⌊(((n : ℝ) - 1)^2 / 4)⌋

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 (by norm_num)
  have ha := result 1 (by norm_num)
  change (⌊(1 : ℝ) / (Real.exp (4 / (1 : ℝ)) - 1)⌋ : ℤ) + 1 = _ at hb
  rw [ha] at hb
  norm_num at hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 3, ?_⟩
  change (⌊(1 : ℝ) / (Real.exp (4 / (1 : ℝ)) - 1)⌋ : ℤ) ≠
    ⌊(3 : ℝ) / (Real.exp (4 / (3 : ℝ)) - 1)⌋
  rw [result 1 (by norm_num), result 3 (by norm_num)]
  norm_num

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := actual_dependence

def audit : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.ForbergExponentialFloor.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.ForbergExponentialFloor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n =>
    ⌊(n : ℝ) / (Real.exp (4 / (n : ℝ)) - 1)⌋) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.ForbergExponentialFloor
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Analytic.SeriesInequalities.ForbergExponentialFloor
