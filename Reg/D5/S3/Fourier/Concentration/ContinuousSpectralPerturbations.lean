import Reg.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
import D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations

/-! Pointwise evaluation of the common continuously perturbed spectrum. -/

namespace Reg.D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight)
open FiniteSpectralPerturbation (actual frequencySignature)
open FiniteSineMissingWindow (sensitivity)
open LeanInformationAudit Finset
open scoped ENNReal

noncomputable section

universe u v

private def rejected : Realization frequencySignature.{u} :=
  realize frequencySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev frequencyArena : Arena where
  signature := frequencySignature.{u}
  Law V := ∀ {J : Type u} {K : Type v} [DecidableEq J]
    [Countable J] [Countable K] (g radius : J → ℝ) (_ : ∀ j, 0 < radius j)
    (support : K → Finset J) (w : ∀ k, support k → ℝ) (_ : ∀ k j, 0 ≤ w k j)
    (p : K → ℕ) (η budget : K → ℝ) (_ : ∀ k, 0 ≤ η k) (_ : ∀ k, 0 < budget k)
    (_ : (∑' k, excessBound (w k) (fun j : support k => radius j) (p k) (η k) /
      ENNReal.ofReal (budget k)) ≤ 1),
    ∃ g' : J → ℝ, (∀ j, |V.readout () ⟨J, g'⟩ j - g j| ≤ radius j) ∧
      ∀ k, tailCollisionMass (fun j : support k => g' j) (w k) (p k) (η k) ≤
        (∑ m ∈ piAntidiag univ (p k), monomialWeight (w k) m ^ 2) + budget k

private theorem rejected_law : ¬ frequencyArena.{u, v}.Law rejected := by
  intro law
  obtain ⟨_, hnear, _⟩ := law (J := ULift.{u} Unit) (K := ULift.{v} Empty)
    (fun _ => 2) (fun _ => 1) (by simp) (fun k => nomatch k.down)
    (fun k => nomatch k.down) (fun k => nomatch k.down)
    0 0 0 (fun k => nomatch k.down) (fun k => nomatch k.down) (by simp)
  have h : |(0 : ℝ) - 2| ≤ 1 := hnear (ULift.up ())
  norm_num at h

def frequencyEvidence :
    Registration frequencyArena.{u, v} (type_of% @exists_continuous_common_nearby_bounds.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_continuous_common_nearby_bounds.{u, v}, rejected, rejected_law⟩
  sensitivity := sensitivity frequencyArena.Law actual rejected rejected_law
  dependence := (FiniteSpectralPerturbation.frequencyEvidence.{u}).dependence

def frequencyRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_continuous_common_nearby_bounds.{u, v}) (Realization frequencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations.frequencyUnit
  realizationName :=
    `Reg.D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations.frequencyEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨frequencyArena.{u, v}⟩
  objectArena := .source ⟨frequencyArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source frequencyArena.{u, v} ⟨frequencyEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations
    definition := none
    coordinates := #[0, 17]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "fn", "arg", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 18
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms frequencyRegistration

end

end Reg.D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations
