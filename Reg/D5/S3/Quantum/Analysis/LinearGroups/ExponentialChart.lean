import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.LinearGroups.ExponentialChart
import Reg.Support.DependentFamily

/-! Source-bound audit of the exponential chart of a locally compact group injecting
continuously into the units of a finite-dimensional real normed algebra. -/

namespace Reg.D5.S3.Quantum.Analysis.LinearGroups.ExponentialChart

open _root_.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators
open _root_.D5.S3.Quantum.Analysis.LinearGroups.ExponentialChart
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v

attribute [local instance] LieRing.ofAssociativeRing

/-! ## Models -/

/-- The real line lifted to universe `u`, a one-dimensional real normed algebra. -/
abbrev Line := ULift.{u} ℝ

/-- The one-point group in universe `v`. -/
abbrev Pt := PUnit.{v + 1}

/-- The trivial homomorphism from the one-point group into the units of `A`. -/
abbrev triv (A : Type u) [NormedRing A] : Pt.{v} →* Aˣ := 1

theorem triv_continuous (A : Type u) [NormedRing A] : Continuous (triv.{u, v} A) :=
  continuous_of_discreteTopology

theorem triv_injective (A : Type u) [NormedRing A] : Function.Injective (triv.{u, v} A) :=
  fun a b _ => Subsingleton.elim a b

/-- The exponential of the lifted real line separates `0` and `1`. -/
theorem exp_zero_ne_exp_one : NormedSpace.exp (0 : Line.{u}) ≠ NormedSpace.exp (1 : Line.{u}) := by
  intro h
  have h' := congrArg (ULift.ringEquiv : ULift.{u} ℝ ≃+* ℝ) h
  rw [NormedSpace.map_exp _ (by exact continuous_uliftDown),
    NormedSpace.map_exp _ (by exact continuous_uliftDown), ← Real.exp_eq_exp_ℝ] at h'
  have := Real.exp_injective h'
  simp at this

/-! ## `exists_exp_chart`: the value prescribed for `ρ (ε X)` as a function of `X` -/
namespace Chart

abbrev signature : Signature where
  Params := Σ A : Type u, NormedRing A
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => letI := p.2; NormedSpace.exp s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

/-- Retain the complete algebra, group, homomorphism and chart telescope of
`exists_exp_chart`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {A : Type u} [iR : NormedRing A] {G : Type v} [TopologicalSpace G] [Group G]
    [NormedAlgebra ℝ A] [FiniteDimensional ℝ A] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (ρ : G →* Aˣ) (hc : Continuous ρ) (hi : Function.Injective ρ),
    ∃ ε : generatorSubalgebra ρ hc hi → G, Continuous ε ∧
      (∀ X, ((ρ (ε X) : Aˣ) : A) = r.readout () ⟨A, iR⟩ (X : A)) ∧
      ∃ U : Set (generatorSubalgebra ρ hc hi), IsOpen U ∧ (0 : generatorSubalgebra ρ hc hi) ∈ U ∧
        Topology.IsOpenEmbedding (U.domRestrict ε)

/-- If `ρ (ε X)` were read as `X` itself, the trivial group in the real line would give
`1 = ρ (ε 0) = 0`. -/
theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  obtain ⟨ε, -, hε, -⟩ := h (A := Line.{u}) (triv.{u, v} Line.{u}) (triv_continuous _)
    (triv_injective _)
  have h0 := hε 0
  simp [rejected, realize] at h0

/-- In the real line the states `0` and `1` have different exponentials. -/
theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  exact ⟨⟨Line.{u}, inferInstance⟩, 0, 1, exp_zero_ne_exp_one⟩

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @exists_exp_chart.{u, v}

def source_registration : Registration arena.{u, v} sourceStatement.{u, v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_exp_chart.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Chart

def exists_exp_chart_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_exp_chart.{u, v}) (Realization Chart.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.LinearGroups.ExponentialChart.exists_exp_chart_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.LinearGroups.ExponentialChart.Chart.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Chart.arena.{u, v}⟩
  objectArena := .source ⟨Chart.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Chart.arena.{u, v} ⟨Chart.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Chart.signature.{u}
    (fun _ p s => letI := p.2; NormedSpace.exp s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.LinearGroups.ExponentialChart
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Analysis.LinearGroups.ExponentialChart
