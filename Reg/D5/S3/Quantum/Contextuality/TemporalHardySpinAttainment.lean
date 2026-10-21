import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment
import Reg.Support.DependentFamily

/-! Source-bound audit of temporal Hardy attainment through state normalization. -/

namespace Reg.D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment
open _root_.D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the squared norm of a spin state in its original dimension. -/
abbrev signature : Signature where
  Params := ℕ
  State n := Fin (n + 1) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ψ => star ψ ⬝ᵥ ψ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Keep every direction, spectral-projector, normalization, and probability clause. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n →
    ∃ (uA₁ uA₂ uB₁ uB₂ : Fin 3 → ℝ) (a₁ a₂ b₁ b₂ : ℝ)
      (PA₁ PA₂ PB₁ PB₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ψ : Fin (n + 1) → ℂ),
      (∑ i, uA₁ i ^ 2 = 1) ∧ (∑ i, uA₂ i ^ 2 = 1) ∧
      (∑ i, uB₁ i ^ 2 = 1) ∧ (∑ i, uB₂ i ^ 2 = 1) ∧
      IsSpectralProjector (spinComponent n uA₁) PA₁ a₁ ∧
      IsSpectralProjector (spinComponent n uA₂) PA₂ a₂ ∧
      IsSpectralProjector (spinComponent n uB₁) PB₁ b₁ ∧
      IsSpectralProjector (spinComponent n uB₂) PB₂ b₂ ∧
      R.readout () n ψ = 1 ∧
      seqProb ψ PA₁ PB₁ = 0 ∧ seqProb ψ (1 - PA₁) PB₂ = 0 ∧
      seqProb ψ PA₂ (1 - PB₁) = 0 ∧ seqProb ψ PA₂ PB₂ = 1 / 4

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h 1 (by norm_num)
  have hnorm := h.2.2.2.2.2.2.2.2.1
  change (0 : ℂ) = 1 at hnorm
  exact zero_ne_one hnorm

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, fun _ => 1, ?_⟩
  change star (0 : Fin (1 + 1) → ℂ) ⬝ᵥ 0 ≠
    star (fun _ : Fin (1 + 1) => (1 : ℂ)) ⬝ᵥ (fun _ => 1)
  norm_num [dotProduct, Fin.sum_univ_two]

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
      (@_root_.D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.source_registration
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
    (realize signature (fun _ _ ψ => star ψ ⬝ᵥ ψ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment
    definition := some {
      owner := `D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment
      name := `D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment
