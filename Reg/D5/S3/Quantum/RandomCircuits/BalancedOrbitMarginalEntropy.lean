import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.RandomCircuits.BalancedOrbitMarginalEntropy
import Reg.Support.DependentFamily

/-! Source-bound audit of the Haar-averaged marginal entropy identity. -/

namespace Reg.D5.S3.Quantum.RandomCircuits.BalancedOrbitMarginalEntropy

open _root_.D5.S3.Quantum.RandomCircuits.BalancedOrbitMarginalEntropy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open _root_.D5.S3.Quantum.Divergence.VonNeumannEntropyPinching (vonNeumannEntropy)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
  (marginalLeft marginalRight)
open _root_.D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
  (unitaryConjugateState)
open Matrix MeasureTheory TopologicalSpace
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the Haar average as its real-valued integrand varies. -/
abbrev signature : Signature where
  Params := ℕ
  State n := Matrix.unitaryGroup (Fin n × Fin n) ℂ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n f => MeasureTheory.integral
    (Measure.haarMeasure (⊤ : PositiveCompacts
      (Matrix.unitaryGroup (Fin n × Fin n) ℂ))) f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ n f => MeasureTheory.integral
    (Measure.haarMeasure (⊤ : PositiveCompacts
      (Matrix.unitaryGroup (Fin n × Fin n) ℂ))) f + 1) (fun e => nomatch e)

/-- Preserve every dimension and density state, replacing only the right-hand integral. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, ∀ ρ : DensityState (Fin n × Fin n),
    (∫ u : Matrix.unitaryGroup (Fin n × Fin n) ℂ,
      vonNeumannEntropy (marginalRight (unitaryConjugateState
        (u : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) u.2 ρ))
      ∂(Measure.haarMeasure (⊤ : PositiveCompacts
        (Matrix.unitaryGroup (Fin n × Fin n) ℂ)))) =
    r.readout () n (fun u : Matrix.unitaryGroup (Fin n × Fin n) ℂ =>
      vonNeumannEntropy (marginalLeft (unitaryConjugateState
        (u : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) u.2 ρ)))

private def singletonState : DensityState (Fin 1 × Fin 1) := by
  refine ⟨1, zero_le_one, ?_⟩
  simp [Matrix.trace, Matrix.diag]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 singletonState
  have htrue := result 1 singletonState
  change _ = _ + (1 : ℝ) at hbad
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  change (∫ _ : Matrix.unitaryGroup (Fin 1 × Fin 1) ℂ, (0 : ℝ)
    ∂(Measure.haarMeasure (⊤ : PositiveCompacts
      (Matrix.unitaryGroup (Fin 1 × Fin 1) ℂ)))) ≠
    ∫ _ : Matrix.unitaryGroup (Fin 1 × Fin 1) ℂ, (1 : ℝ)
      ∂(Measure.haarMeasure (⊤ : PositiveCompacts
        (Matrix.unitaryGroup (Fin 1 × Fin 1) ℂ)))
  simp

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
      (@_root_.D5.S3.Quantum.RandomCircuits.BalancedOrbitMarginalEntropy.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.RandomCircuits.BalancedOrbitMarginalEntropy.unit
  realizationName :=
    `Reg.D5.S3.Quantum.RandomCircuits.BalancedOrbitMarginalEntropy.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n f => MeasureTheory.integral
    (Measure.haarMeasure (⊤ : PositiveCompacts
      (Matrix.unitaryGroup (Fin n × Fin n) ℂ))) f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.RandomCircuits.BalancedOrbitMarginalEntropy
    definition := some {
      owner := `D5.S3.Quantum.RandomCircuits.BalancedOrbitMarginalEntropy
      name := `D5.S3.Quantum.RandomCircuits.BalancedOrbitMarginalEntropy.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
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
end Reg.D5.S3.Quantum.RandomCircuits.BalancedOrbitMarginalEntropy
