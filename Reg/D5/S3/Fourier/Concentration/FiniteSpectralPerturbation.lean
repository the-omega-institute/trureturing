import Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow
import D5.S3.Fourier.Concentration.FiniteSpectralPerturbation

/-! Pointwise observation of the nearby spectrum in the perturbation theorem. -/

namespace Reg.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open FiniteSineMissingWindow (oneRole sensitivity)
open LeanInformationAudit Finset

noncomputable section

universe u

abbrev frequencySignature : Signature :=
  oneRole (Σ J : Type u, J → ℝ) Sigma.fst

def actual : Realization frequencySignature.{u} :=
  realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e)

private def rejected : Realization frequencySignature.{u} :=
  realize frequencySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev frequencyArena : Arena where
  signature := frequencySignature.{u}
  Law V := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (_ : ∀ j, 0 ≤ w j) (p M : ℕ)
    {ε η : ℝ} (_ : 0 < ε) (_ : 0 ≤ η),
    let W := ∑ j, w j
    let D := ∑ m ∈ piAntidiag univ p, monomialWeight w m ^ 2
    ∃ g' : J → ℝ,
      (∀ j, |V.readout () ⟨J, g'⟩ j - g j| ≤ ε) ∧
      tailCollisionMass g' w p η ≤
        D + (((min (M + 2) (1 + ⌊η * ((M : ℝ) + 1) / ε⌋₊) : ℕ) : ℝ) / (M + 2)) *
          (W ^ (2 * p) - D)

private theorem rejected_law : ¬ frequencyArena.{u}.Law rejected := by
  intro law
  obtain ⟨g', hnear, _⟩ := law (J := ULift.{u} Unit) (fun _ => 2) 0 (by simp) 1 0
    (ε := 1) (η := 0) zero_lt_one le_rfl
  have h : |(0 : ℝ) - 2| ≤ 1 := hnear (ULift.up ())
  norm_num at h

private theorem frequency_dependence : ObservationalDependence frequencySignature.{u} actual := by
  intro _
  refine ⟨⟨ULift.{u} Bool, fun j => if j.down then 1 else 0⟩, ULift.up false, ULift.up true, ?_⟩
  change (0 : ℝ) ≠ 1
  norm_num

def frequencyEvidence :
    Registration frequencyArena.{u} (type_of% @exists_nearby_collision_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_nearby_collision_bound.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity frequencyArena.Law actual rejected rejected_law
  dependence := frequency_dependence

def frequencyRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_nearby_collision_bound.{u}) (Realization frequencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation.frequencyUnit
  realizationName :=
    `Reg.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation.frequencyEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨frequencyArena.{u}⟩
  objectArena := .source ⟨frequencyArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source frequencyArena.{u} ⟨frequencyEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
    definition := none
    coordinates := #[0, 14]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms frequencyRegistration

end

end Reg.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
