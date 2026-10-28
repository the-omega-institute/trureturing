import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound
import Reg.Support.DependentFamily

/-! Source-bound audit of the entanglement-buffer availability lower bound. -/

namespace Reg.D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound

open _root_.D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe availability as the purification probability varies. -/
abbrev signature : Signature where
  Params := Σ n : ℕ, Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ,
    Σ _ : Fin n → ℝ, Σ _ : Fin n → ℝ, Σ _ : Fin n → ℝ, Fin n → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p q =>
    availability p.1 p.2.1 p.2.2.1 q p.2.2.2.1 p.2.2.2.2.1
      p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain every parameter constraint and the always-failing comparison policy. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 1 ≤ n → ∀ (pg pc gam fnew : ℝ),
    0 < pg → pg ≤ 1 → 0 < pc → pc ≤ 1 → 0 ≤ gam → 1 / 4 < fnew → fnew ≤ 1 →
    ∀ (a b c d : Fin n → ℝ), admissible a b c d → ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
    availability n pg pc 1 gam fnew 0 0 0 0 ≤
      R.readout () ⟨n, pg, pc, gam, fnew, a, b, c, d⟩ q

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha : admissible (0 : Fin 1 → ℝ) 0 0 0 := by
    intro k f hf hf1
    norm_num
  have hbad := h 1 (by norm_num) 1 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) 0 0 0 0 ha 1
    (by norm_num) (by norm_num)
  change availability 1 1 1 1 0 1 0 0 0 0 ≤ 0 at hbad
  norm_num [availability, dotProduct] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1, 1 / 2, 0, 1, 0, 0, 0, 0⟩, 0, 1, ?_⟩
  change availability 1 1 (1 / 2) 0 0 1 0 0 0 0 ≠
    availability 1 1 (1 / 2) 1 0 1 0 0 0 0
  norm_num [availability, dotProduct]

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
      (@_root_.D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p q =>
    availability p.1 p.2.1 p.2.2.1 q p.2.2.2.1 p.2.2.2.2.1
      p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound
    definition := some {
      owner := `D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound
      name := `D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound.claim
      path := #[] }
    coordinates := #[0, 2, 3, 4, 5, 13, 14, 15, 16]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 18
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Decoherence.EntanglementBufferAvailabilityLowerBound
