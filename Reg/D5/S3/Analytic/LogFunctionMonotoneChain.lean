import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.LogFunctionMonotoneChain
import Reg.Support.DependentFamily

/-! Source-bound audit of the intersection characterization for polynomial log-functions. -/

namespace Reg.D5.S3.Analytic.LogFunctionMonotoneChain

open _root_.D5.S3.Analytic.LogFunctionMonotoneChain
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe a polynomial log-function at a real argument. -/
abbrev signature : Signature where
  Params := Polynomial ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => logFunction p x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain every degree bound, nesting clause and intersection equivalence. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    (∀ k : ℕ, 1 ≤ k → derivativeRegion n (k + 1) ⊆ derivativeRegion n k) ∧
    ∀ p : Polynomial ℝ, p.natDegree ≤ n →
      ((∀ k : ℕ, 1 ≤ k → p ∈ derivativeRegion n k) ↔
        completelyMonotone (R.readout () p))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : (-1 : Polynomial ℝ).natDegree ≤ 0 := by simp
  have hz : completelyMonotone (rejected.readout () (-1)) := by
    intro k x _
    simp [rejected, realize]
  have hregions := ((h 0).2 (-1) hp).mpr hz
  have hmono := ((result 0).2 (-1) hp).mp hregions
  have hbad := hmono 0 1 (by norm_num)
  norm_num [logFunction] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  change logFunction 1 1 ≠ logFunction 1 2
  norm_num [logFunction]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.LogFunctionMonotoneChain.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.LogFunctionMonotoneChain.unit
  realizationName := `Reg.D5.S3.Analytic.LogFunctionMonotoneChain.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => logFunction p x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.LogFunctionMonotoneChain
    definition := some {
      owner := `D5.S3.Analytic.LogFunctionMonotoneChain
      name := `D5.S3.Analytic.LogFunctionMonotoneChain.claim
      path := #[] }
    coordinates := #[1]
    readouts := #[{
      path := #["body", "arg", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Analytic.LogFunctionMonotoneChain
