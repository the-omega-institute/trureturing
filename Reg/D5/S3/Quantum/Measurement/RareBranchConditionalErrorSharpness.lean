import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
open _root_.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness
open Filter Lean Elab Command LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Topology

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ε => ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ ε : ℝ, 0 < ε → ε < 1 →
      let C : Matrix (Fin 3) (Fin 3) ℂ := basisProjector 0
      let E0 : Matrix (Fin 3) (Fin 3) ℂ := basisProjector 1
      let E1 : Matrix (Fin 3) (Fin 3) ℂ := basisProjector 2
      let rhoM : Matrix (Fin 3) (Fin 3) ℂ := diagonalState (fun i =>
        if i = 0 then 1 - ε else if i = 1 then ε else 0)
      let sigmaM : Matrix (Fin 3) (Fin 3) ℂ := diagonalState (fun i =>
        if i = 0 then 1 - ε else if i = 2 then ε else 0)
      let P : Matrix (Fin 3) (Fin 3) ℂ := E0 + E1
      ∃ ρ σ : DensityState (Fin 3), ∃ Pm K : Matrix (Fin 3) (Fin 3) ℂ,
        CStarMatrix.ofMatrix.symm ρ.val = rhoM ∧
        CStarMatrix.ofMatrix.symm σ.val = sigmaM ∧
        Pm = P ∧ K = C ∧
        Pmᴴ * Pm + Kᴴ * K = 1 ∧
        Pmᴴ * Pm ≤ 1 ∧
        traceDistance ρ σ = R.readout () () ε ∧
        (CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ * Pm).trace.re = ε ∧
        (CStarMatrix.ofMatrix.symm σ.val * Pmᴴ * Pm).trace.re = ε ∧
        (1 / ε : ℝ) •
            (Pm * CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ) = E0 ∧
        (1 / ε : ℝ) •
            (Pm * CStarMatrix.ofMatrix.symm σ.val * Pmᴴ) = E1 ∧
        traceNorm (E0 - E1) / 2 = 1 ∧
        max ε ε * (traceNorm (
          (1 / ε : ℝ) • (Pm * CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ) -
          (1 / ε : ℝ) • (Pm * CStarMatrix.ofMatrix.symm σ.val * Pmᴴ)) / 2) =
          traceDistance ρ σ) ∧
    ¬ ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧
      ∀ ρ σ : DensityState (Fin 3),
        ∀ Pm : Matrix (Fin 3) (Fin 3) ℂ,
          Pmᴴ * Pm ≤ 1 →
          0 < (CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ * Pm).trace.re →
          0 < (CStarMatrix.ofMatrix.symm σ.val * Pmᴴ * Pm).trace.re →
          traceNorm (
            (1 / (CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ * Pm).trace.re : ℝ) •
              (Pm * CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ) -
            (1 / (CStarMatrix.ofMatrix.symm σ.val * Pmᴴ * Pm).trace.re : ℝ) •
              (Pm * CStarMatrix.ofMatrix.symm σ.val * Pmᴴ)) / 2 ≤
            f (traceDistance ρ σ)

theorem actual_law : arena.Law actual := by
  simpa [arena, actual, realize, signature] using
    rare_branch_conditional_error_sharpness

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change _ ∧ _ at h
  have hcase := h.1 (1 / 2 : ℝ) (by norm_num) (by norm_num)
  dsimp only at hcase
  obtain ⟨ρ, σ, Pm, K, _hρ, _hσ, _hP, _hK, _hinst, _hbound, hD,
    _hp, _hq, hcondρ, hcondσ, hunit, hw⟩ := hcase
  have hweight := hw
  rw [hcondρ, hcondσ, hunit, hD] at hweight
  simp [rejected, realize, signature] at hweight

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨(), (1 : ℝ), (2 : ℝ), by
      change (1 : ℝ) ≠ 2
      norm_num⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.rare_branch_conditional_error_sharpness) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ ε => ε) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "RareBranchConditionalErrorSharpness") "rare_branch_conditional_error_sharpness") "Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness/Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ ε => ε) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms actual_law
#print axioms rejected_law

end Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness
