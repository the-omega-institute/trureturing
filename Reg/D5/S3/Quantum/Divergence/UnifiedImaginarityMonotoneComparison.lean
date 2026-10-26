import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison
import Reg.Support.DependentFamily

/-! Source-bound audit of the unified imaginarity comparison. -/

namespace Reg.D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison

open _root_.D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison
open _root_.D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open _root_.D5.S3.Quantum.Tomography.MUB.MUBCompletionRelativeGramEquivalence
  (entrywiseConj)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe conjugate divergence at every dimension and pair of real parameters. -/
abbrev signature : Signature where
  Params := Σ _d : ℕ, Σ _α : ℝ, ℝ
  State p := Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p ρ => imaginarityH p.2.1 p.2.2 ρ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Keep all density, dimension, and parameter hypotheses of the comparison. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (d : ℕ), 1 ≤ d → ∀ ρ : Matrix (Fin d) (Fin d) ℂ, IsDensity ρ →
    ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ β ∈ Set.Ioc (0 : ℝ) 1,
      imaginarityE α β ρ ≤ r.readout () ⟨d, α, β⟩ ρ

private theorem scalar_density : IsDensity (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  exact ⟨Matrix.PosSemidef.one, by simp⟩

private theorem scalar_state_eq_one {σ : Matrix (Fin 1) (Fin 1) ℂ}
    (hσ : IsDensity σ) : σ = 1 := by
  have hentry : σ 0 0 = 1 := by simpa [Matrix.trace] using hσ.2
  ext i j
  fin_cases i
  fin_cases j
  simpa using hentry

private theorem scalar_imaginarityE :
    imaginarityE (1 / 2) 1 (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
  have hconj : entrywiseConj (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [entrywiseConj]
  have hdiv : unifiedDivergence (1 / 2) 1
      (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 0 := by
    norm_num [unifiedDivergence, CFC.one_rpow]
  have hset : {x : ℝ | ∃ σ : Matrix (Fin 1) (Fin 1) ℂ,
      IsDensity σ ∧ entrywiseConj σ = σ ∧
        x = unifiedDivergence (1 / 2) 1 1 σ} = {0} := by
    ext x
    constructor
    · rintro ⟨σ, hσ, _, rfl⟩
      rw [scalar_state_eq_one hσ, hdiv]
      exact Set.mem_singleton 0
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨1, scalar_density, hconj, by simpa [hx] using hdiv.symm⟩
  unfold imaginarityE
  rw [hset, csInf_singleton]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (by norm_num) 1 scalar_density (1 / 2) (by norm_num)
    1 (by norm_num)
  change imaginarityE (1 / 2) 1 (1 : Matrix (Fin 1) (Fin 1) ℂ) ≤ -1 at hbad
  rw [scalar_imaginarityE] at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1 / 2, 1⟩, 0, 1, ?_⟩
  change imaginarityH (1 / 2) 1 (0 : Matrix (Fin 1) (Fin 1) ℂ) ≠
    imaginarityH (1 / 2) 1 (1 : Matrix (Fin 1) (Fin 1) ℂ)
  have hzero : entrywiseConj (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    ext i j
    simp [entrywiseConj]
  have hone : entrywiseConj (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [entrywiseConj]
  have hpow : (0 : Matrix (Fin 1) (Fin 1) ℂ) ^ (1 / 2 : ℝ) = 0 :=
    CFC.zero_rpow (by norm_num)
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  simp only [imaginarityH, unifiedDivergence, hzero, hone, hhalf, hpow,
    CFC.one_rpow, zero_mul, one_mul, Matrix.trace_zero, Matrix.trace_one]
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
      (@_root_.D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.source_registration
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
    (realize signature (fun _ p ρ => imaginarityH p.2.1 p.2.2 ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison
    definition := some {
      owner := `D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison
      name := `D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison.claim
      path := #[] }
    coordinates := #[0, 4, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison
