import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder
import Reg.Support.SingleDependentReadout

/-! # Whole-sequence observation of the original Gurland remainder -/


namespace Reg.D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder
open _root_.D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter
open scoped Topology
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ)
    (fun _ => ℝ → ℝ → ℕ → ℝ) (fun _ => ℕ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ p s => s p.1 p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ x y : ℝ, 0 < x → 0 < y →
    Tendsto (R.readout () ⟨x, y⟩ remainder) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 1 (by norm_num) (by norm_num)
  change Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) at hbad
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have heq := tendsto_nhds_unique hone hbad
  norm_num at heq

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0⟩, (fun _ _ _ => 0), (fun _ _ _ => 1), ?_⟩
  change (fun _ : ℕ => (0 : ℝ)) ≠ (fun _ : ℕ => (1 : ℝ))
  intro h
  have heq := congrFun h 0
  norm_num at heq

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.result)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s => s p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder
    definition := some {
      owner := `D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder
      name := `D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.claim
      path := #[] }
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms result
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder
