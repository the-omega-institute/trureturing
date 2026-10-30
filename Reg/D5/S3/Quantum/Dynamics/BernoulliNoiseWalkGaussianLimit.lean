import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit
import Reg.Support.DependentFamily

/-! Source-bound audit of the Gaussian limit value of the Bernoulli noise walk. -/

namespace Reg.D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit

open _root_.D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit
open _root_.D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the standard Gaussian integral of a bounded continuous test function. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ →ᵇ ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => ∫ y, f y ∂(gaussianReal 0 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (φ : ObserverHilbertSpace (Finset ℕ)), ‖φ‖ = 1 → ∀ f : ℝ →ᵇ ℝ,
    Tendsto (fun n : ℕ => ∫ y, f y ∂(walkLaw φ n)) atTop (𝓝 (r.readout () () f))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let φ : ObserverHilbertSpace (Finset ℕ) := lp.single 2 ∅ (1 : ℂ)
  have hφ : ‖φ‖ = 1 := by
    simpa only [φ, norm_one] using
      (lp.norm_single (E := fun _ : Finset ℕ => ℂ) (by norm_num)
        ∅ (1 : ℂ))
  have hzero := h φ hφ (1 : ℝ →ᵇ ℝ)
  have hone := result φ hφ (1 : ℝ →ᵇ ℝ)
  have heq := tendsto_nhds_unique hone hzero
  norm_num [actual, rejected, realize, BoundedContinuousFunction.coe_one] at heq

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (∫ _ : ℝ, (0 : ℝ) ∂(gaussianReal 0 1)) ≠
    ∫ _ : ℝ, (1 : ℝ) ∂(gaussianReal 0 1)
  norm_num

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit.source_registration
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
    (fun _ _ f => ∫ y, f y ∂(gaussianReal 0 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
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
end Reg.D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit
