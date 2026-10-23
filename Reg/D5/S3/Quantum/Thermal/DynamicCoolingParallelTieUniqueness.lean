import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness
open _root_.D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The parallel response function is observed at the thermal population coordinate. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _N : ℕ, Σ _M : ℕ, ℝ)
    (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p f => f p.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => pGlob p.1 p.2.1 p.2.2) (fun e => nomatch e)

/-- Retain every parameter and hypothesis, replacing only the parallel benchmark observation. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ N M : ℕ, 2 ≤ M → M + 2 ≤ N → (N, M) ≠ (6, 2) →
    ∀ P₁ : ℝ, 0 < P₁ → P₁ < 1 / 2 →
      pGlob N M P₁ < R.readout () ⟨N, M, P₁⟩ (pGlob (N / M) 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 4 2 (by norm_num) (by norm_num) (by norm_num)
    (1 / 4) (by norm_num) (by norm_num)
  exact lt_irrefl (pGlob 4 2 (1 / 4)) hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨4, 2, 1 / 4⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  exact zero_ne_one

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p f => f p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness
    definition := some {
      owner := `D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness
      name := `D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.claim
      path := #[] }
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms signature
#print axioms actual
#print axioms rejected
#print axioms arena
#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness
