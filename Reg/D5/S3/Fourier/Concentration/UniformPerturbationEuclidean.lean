import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Fourier.Concentration.UniformPerturbationEuclidean

/-! The readout is the probability of the affine band under the original product law. -/

namespace Reg.D5.S3.Fourier.Concentration.UniformPerturbationEuclidean

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations
open _root_.D5.S3.Fourier.Concentration.UniformPerturbationEuclidean
open LeanInformationAudit MeasureTheory Finset Set
open scoped ENNReal

noncomputable section

universe u

abbrev bandSignature : Signature where
  Params := Σ J : Type u, Σ _ : Fintype J, J → ℝ
  State q := Set (q.1 → ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization bandSignature.{u} :=
  realize bandSignature
    (fun _ q W => let _ := q.2.1; (Measure.pi fun j => intervalNoise (q.2.2 j)) W)
    (fun e => nomatch e)

private def rejected : Realization bandSignature.{u} :=
  realize bandSignature (fun _ _ _ => (1 : ℝ≥0∞)) (fun e => nomatch e)

abbrev bandArena : Arena where
  signature := bandSignature.{u}
  Law A := ∀ {J : Type u} [i : Fintype J] (r a : J → ℝ)
    (_ : ∀ j, 0 < r j) (b : ℝ) {η : ℝ} (_ : 0 ≤ η)
    (_ : 0 < ∑ j, (a j * r j) ^ 2),
    A.readout () ⟨J, i, r⟩ {x | |(∑ j, a j * x j) + b| ≤ η} ≤
      min 1 (ENNReal.ofReal
        (Real.exp (1 / 2) * Real.sqrt (15 * Real.pi / 2) * η /
          Real.sqrt (∑ j, (a j * r j) ^ 2)))

private theorem rejected_law : ¬ bandArena.{u}.Law rejected := by
  intro law
  have h := law (J := ULift.{u} Unit) 1 1 (fun _ => zero_lt_one) 0 (η := 0) le_rfl
    (by simp)
  change (1 : ℝ≥0∞) ≤ min 1 (ENNReal.ofReal
    (Real.exp (1 / 2) * Real.sqrt (15 * Real.pi / 2) * 0 /
      Real.sqrt (∑ _ : ULift.{u} Unit, ((1 : ℝ) * 1) ^ 2))) at h
  simp at h

private theorem dependence : ObservationalDependence bandSignature.{u} actual := by
  intro _
  refine ⟨⟨ULift.{u} Unit, inferInstance, 1⟩, univ, ∅, ?_⟩
  change (Measure.pi fun _ : ULift.{u} Unit => intervalNoise 1) univ ≠
    (Measure.pi fun _ : ULift.{u} Unit => intervalNoise 1) ∅
  have (_ : ULift.{u} Unit) : IsProbabilityMeasure (intervalNoise 1) :=
    intervalNoise_probability zero_lt_one
  simp

def bandEvidence :
    Registration bandArena.{u} (type_of% @intervalNoise_pi_affine_le_euclidean.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@intervalNoise_pi_affine_le_euclidean.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, ?_, rejected_law⟩
      funext e
      exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def bandRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@intervalNoise_pi_affine_le_euclidean.{u}) (Realization bandSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.UniformPerturbationEuclidean.bandUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.UniformPerturbationEuclidean.bandEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨bandArena.{u}⟩
  objectArena := .source ⟨bandArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source bandArena.{u} ⟨bandEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize bandSignature
    (fun _ q W => let _ := q.2.1; (Measure.pi fun j => intervalNoise (q.2.2 j)) W)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.UniformPerturbationEuclidean
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms bandRegistration

end

end Reg.D5.S3.Fourier.Concentration.UniformPerturbationEuclidean
