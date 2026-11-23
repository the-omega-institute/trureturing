import Reg.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
import D5.S3.Fourier.Concentration.CommonSpectralPerturbations

/-! The shared perturbed spectrum is observed by evaluation at each coordinate. -/

namespace Reg.D5.S3.Fourier.Concentration.CommonSpectralPerturbations

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.CommonSpectralPerturbations
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open FiniteSpectralPerturbation (actual frequencySignature)
open FiniteSineMissingWindow (sensitivity)
open LeanInformationAudit Finset

noncomputable section

universe u v

private def rejected : Realization frequencySignature.{u} :=
  realize frequencySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev frequencyArena : Arena where
  signature := frequencySignature.{u}
  Law V := ∀ {J : Type u} {K : Type v} [DecidableEq J]
    (M : J → ℕ) (g ε : J → ℝ) (_ : ∀ j, 0 < ε j)
    (support : K → Finset J) (w : ∀ k, support k → ℝ)
    (_ : ∀ k j, 0 ≤ w k j) (p : K → ℕ) (η ρ b : K → ℝ)
    (_ : ∀ k, 0 ≤ η k) (_ : ∀ k, 0 < b k)
    (_ : ∀ k (j : support k),
      ((min (M j + 2) (1 + ⌊η k * ((M j : ℝ) + 1) / ε j⌋₊) : ℕ) : ℝ) /
        (M j + 2) ≤ ρ k)
    (_ : ∀ tests : Finset K, ∑ k ∈ tests,
      (if 0 < offDiagonalMass (w k) (p k) then ρ k / b k else 0) ≤ 1),
    ∃ g' : J → ℝ, (∀ j, |V.readout () ⟨J, g'⟩ j - g j| ≤ ε j) ∧
      (∃ f : (j : J) → Fin (M j + 2), ∀ j,
        g' j = g j + ε j * (2 * ((f j).val : ℝ) / ((M j : ℝ) + 1) - 1)) ∧
      ∀ k, tailCollisionMass (fun j : support k => g' j) (w k) (p k) (η k) ≤
        diagonalMass (w k) (p k) + b k * offDiagonalMass (w k) (p k)

private theorem rejected_law : ¬ frequencyArena.{u, v}.Law rejected := by
  intro law
  obtain ⟨_, hnear, _⟩ := law (J := ULift.{u} Unit) (K := ULift.{v} Empty)
    0 (fun _ => 2) (fun _ => 1) (by simp) (fun k => nomatch k.down)
    (fun k => nomatch k.down) (fun k => nomatch k.down)
    0 0 0 0 (fun k => nomatch k.down) (fun k => nomatch k.down)
    (fun k => nomatch k.down) (by simp)
  have h : |(0 : ℝ) - 2| ≤ 1 := hnear (ULift.up ())
  norm_num at h

def frequencyEvidence :
    Registration frequencyArena.{u, v} (type_of% @exists_common_nearby_collision_bounds.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_common_nearby_collision_bounds.{u, v}, rejected, rejected_law⟩
  sensitivity := sensitivity frequencyArena.Law actual rejected rejected_law
  dependence := (FiniteSpectralPerturbation.frequencyEvidence.{u}).dependence

def frequencyRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_common_nearby_collision_bounds.{u, v}) (Realization frequencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CommonSpectralPerturbations.frequencyUnit
  realizationName :=
    `Reg.D5.S3.Fourier.Concentration.CommonSpectralPerturbations.frequencyEvidence
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
    owner := `D5.S3.Fourier.Concentration.CommonSpectralPerturbations
    definition := none
    coordinates := #[0, 18]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "fn", "arg", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 19
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms frequencyRegistration

end

end Reg.D5.S3.Fourier.Concentration.CommonSpectralPerturbations
