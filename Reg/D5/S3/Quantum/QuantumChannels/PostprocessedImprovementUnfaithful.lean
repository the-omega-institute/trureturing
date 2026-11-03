import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful
import Reg.Support.DependentFamily

/-! Source-bound audit of zero optimized improvement for coherence-creating channels. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful

open _root_.D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful
open _root_.D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue (IsChannel)
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe real equality in the zero-improvement conclusion. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Retain every biased prior, output dimension, phase, and channel constraint. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (l : ℝ), 0 ≤ l → l ≤ 1 → l ≠ 1 / 2 →
    ∀ (m : ℕ), 1 ≤ m → ∀ (φ : Fin m → ℝ),
      ∃ θ : MatrixMap (Fin 2) (Fin 2) ℂ,
        IsChannel θ ∧ ¬ IsMIO θ ∧ R.readout () () (postImprovement l φ θ) 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨θ, _, _, hfalse⟩ := h 0 (by norm_num) (by norm_num) (by norm_num)
    1 (by norm_num) (fun _ => 0)
  exact hfalse

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hfalse : (1 : ℝ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero hfalse

def source_registration : Registration arena (type_of% @result) where
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
      (@_root_.D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "fn", "fn"]
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
end Reg.D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful
