import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.NonUnitalNetworkConditionImplication
import Reg.Support.DependentFamily

/-! Source-bound audit of the quadratic network nonlocality-breaking bound. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.NonUnitalNetworkConditionImplication

open _root_.D5.S3.Quantum.QuantumChannels.NonUnitalNetworkConditionImplication
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Fix the translation and first contraction, and vary the third contraction. -/
abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p l3 => (|p.1| + |l3|) ^ 2 + p.2 ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- Retain all three channel constraints and both conclusions. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ t l1 l3 : ℝ,
    |l1| ≤ 1 →
    |l3| + |t| ≤ 1 →
    l1 ^ 2 + t ^ 2 ≤ (1 - |l3|) ^ 2 →
    r.readout () ⟨t, l1⟩ l3 ≤ 1 ∧
      2 * t ^ 2 * l1 ^ 2 + l1 ^ 4 + (|t| + |l3|) ^ 4 ≤ 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 0 0 0 (by norm_num) (by norm_num) (by norm_num)).1
  change (2 : ℝ) ≤ 1 at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
  change (|(0 : ℝ)| + |(0 : ℝ)|) ^ 2 + (0 : ℝ) ^ 2 ≠
    (|(0 : ℝ)| + |(1 : ℝ)|) ^ 2 + (0 : ℝ) ^ 2
  norm_num

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
      (@_root_.D5.S3.Quantum.QuantumChannels.NonUnitalNetworkConditionImplication.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.NonUnitalNetworkConditionImplication.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.NonUnitalNetworkConditionImplication.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p l3 => (|p.1| + |l3|) ^ 2 + p.2 ^ 2)
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.NonUnitalNetworkConditionImplication
    definition := some {
      owner := `D5.S3.Quantum.QuantumChannels.NonUnitalNetworkConditionImplication
      name := `D5.S3.Quantum.QuantumChannels.NonUnitalNetworkConditionImplication.claim
      path := #[] }
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.NonUnitalNetworkConditionImplication
