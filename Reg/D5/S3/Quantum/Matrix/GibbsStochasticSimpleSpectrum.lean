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

/-- Observe the admissible processes as the Gibbs weight vector varies. -/
abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Set (Matrix (Fin n) (Fin n) ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => thermalProcesses d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

/-- Retain every dimension, positive weight vector, and Gibbs-stochastic condition. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (d : Fin n → ℝ), (∀ i, 0 < d i) →
    ∃ P : Matrix (Fin n) (Fin n) ℝ,
      P ∈ R.readout () n d ∧ HasSimpleEigenvalues P

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨P, hbad, _⟩ := h 1 (fun _ => 1) (by intro i; norm_num)
  exact hbad

private def reset : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i _ => if i = 0 then 1 else 0

theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hstochastic : reset ∈ Matrix.colStochastic ℝ (Fin 2) := by
    apply Matrix.mem_colStochastic_iff_sum.mpr
    constructor
    · intro i j
      simp only [reset]
      split_ifs <;> norm_num
    · intro j
      norm_num [reset, Fin.sum_univ_two]
  have hzero : reset ∈ thermalProcesses (0 : Fin 2 → ℝ) :=
    ⟨hstochastic, Matrix.mulVec_zero reset⟩
  have hone : reset ∉ thermalProcesses (fun _ : Fin 2 => 1) := by
    intro h
    have hbad := congrFun h.2 (0 : Fin 2)
    norm_num [reset, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hbad
  refine ⟨2, 0, fun _ => 1, ?_⟩
  change thermalProcesses (0 : Fin 2 → ℝ) ≠ thermalProcesses (fun _ : Fin 2 => 1)
  intro heq
  exact hone (heq ▸ hzero)

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
  readout := some
    (realize signature (fun _ _ d => thermalProcesses d) (fun e => nomatch e))
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
      path := #["body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum
