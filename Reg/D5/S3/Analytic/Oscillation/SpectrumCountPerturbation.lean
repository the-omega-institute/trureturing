import Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow
import D5.S3.Analytic.Oscillation.SpectrumCountPerturbation

/-! The relocated ordinates must realize the prescribed frequencies. -/

namespace Reg.D5.S3.Analytic.Oscillation.SpectrumCountPerturbation

open _root_.D5.S3.Analytic.Oscillation.OrdinateCounting
open _root_.D5.S3.Analytic.Oscillation.SpectrumCountPerturbation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow (oneRole sensitivity)
open LeanInformationAudit

noncomputable section

abbrev frequencySignature : Signature :=
  oneRole (Σ S : Spectrum, S.index → ℝ) (fun q => q.1.index)

def actual : Realization frequencySignature :=
  realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e)

private def rejected : Realization frequencySignature :=
  realize frequencySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev frequencyArena : Arena where
  signature := frequencySignature
  Law V := ∀ S : Spectrum,
    ∃ r : S.index → ℝ, (∀ j, 0 < r j ∧ r j ≤ 1 / 3 ∧ r j < S.gamma j) ∧
      (∀ i j, S.gamma i < S.gamma j → S.gamma i + r i < S.gamma j - r j) ∧
      ∀ g' : S.index → ℝ, (∀ j, |g' j - S.gamma j| ≤ r j) →
        ∃ (S' : Spectrum) (e : S.index ≃ S'.index),
          (∀ j, S'.gamma (e j) = V.readout () ⟨S, g'⟩ j ∧ S'.mult (e j) = S.mult j) ∧
          (∀ i j, g' i < g' j ↔ S.gamma i < S.gamma j) ∧
          ∀ T, S'.N T = S.N T ∨
            ∃ j, T ∈ Set.Ico (S.gamma j - r j) (S.gamma j + r j) ∧
              (S'.N T + S.mult j = S.N T ∨ S.N T + S.mult j = S'.N T)

private def twoPoints : Spectrum where
  index := Fin 2
  gamma j := (j.val : ℝ) + 1
  mult _ := 1
  gamma_pos _ := by positivity
  gamma_injective := by
    intro i j h
    apply Fin.ext
    exact_mod_cast add_right_cancel h
  mult_pos _ := Nat.one_pos
  finite_le _ := Set.toFinite _

private theorem rejected_law : ¬ frequencyArena.Law rejected := by
  intro law
  obtain ⟨r, hr, _, h⟩ := law twoPoints
  obtain ⟨S', e, hrep, _⟩ := h twoPoints.gamma (fun j => by simpa using (hr j).1.le)
  exact (S'.gamma_pos (e (0 : Fin 2))).ne' (hrep (0 : Fin 2)).1

private theorem frequency_dependence : ObservationalDependence frequencySignature actual := by
  intro _
  refine ⟨⟨twoPoints, twoPoints.gamma⟩, (0 : Fin 2), (1 : Fin 2), ?_⟩
  change twoPoints.gamma (0 : Fin 2) ≠ twoPoints.gamma (1 : Fin 2)
  exact twoPoints.gamma_injective.ne (by decide : (0 : Fin 2) ≠ 1)

def frequencyEvidence :
    Registration frequencyArena (type_of% @exists_ordered_count_perturbations) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_ordered_count_perturbations, rejected, rejected_law⟩
  sensitivity := sensitivity frequencyArena.Law actual rejected rejected_law
  dependence := frequency_dependence

def frequencyRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_ordered_count_perturbations) (Realization frequencySignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Oscillation.SpectrumCountPerturbation.frequencyUnit
  realizationName := `Reg.D5.S3.Analytic.Oscillation.SpectrumCountPerturbation.frequencyEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨frequencyArena⟩
  objectArena := .source ⟨frequencyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source frequencyArena ⟨frequencyEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Oscillation.SpectrumCountPerturbation
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "arg", "body", "body", "arg", "body",
        "arg", "body", "fn", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms frequencyRegistration

end

end Reg.D5.S3.Analytic.Oscillation.SpectrumCountPerturbation
