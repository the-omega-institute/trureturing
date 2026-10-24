import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum
import Reg.Support.DependentFamily

/-! Source-bound audit of simple spectrum for Gibbs-stochastic matrices. -/

namespace Reg.D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum

open _root_.D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum
open _root_.D5.S3.StatisticalMechanics.ThermalProcessSelfDualFactorizationRefutation
  (thermalProcesses)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe whether the complex characteristic polynomial has distinct roots. -/
abbrev signature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ _ P => @decide (HasSimpleEigenvalues P) (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- Retain every dimension, positive weight vector, and Gibbs-stochastic condition. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (d : Fin n → ℝ), (∀ i, 0 < d i) →
    ∃ P : Matrix (Fin n) (Fin n) ℝ,
      P ∈ thermalProcesses d ∧ R.readout () n P = true

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨P, _, hbad⟩ := h 1 (fun _ => 1) (by intro i; norm_num)
  change false = true at hbad
  cases hbad

private theorem zero_not_simple :
    ¬ HasSimpleEigenvalues (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hmap : (0 : Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℂ) = 0 := by
    ext i j
    simp
  unfold HasSimpleEigenvalues
  rw [hmap, Matrix.charpoly_zero, Fintype.card_fin, Polynomial.roots_X_pow]
  norm_num [two_smul]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨P, _, hP⟩ := result 2 (fun _ => 1) (by intro j; norm_num)
  refine ⟨2, P, 0, ?_⟩
  simp [actual, realize, hP, zero_not_simple]

def source_registration : Registration arena claim where
  actual := actual
  bridge := by simp [claim, actual, realize]
  variation := ⟨by simpa [claim, actual, realize] using result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ P => @decide (HasSimpleEigenvalues P) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum
    definition := some {
      owner := `D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum
      name := `D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum
