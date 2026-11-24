import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.EvenHarmonicFirstMoment

/-! Dependence of the sharp first coefficient on the length of the even block. -/

namespace Reg.D5.S3.Fourier.Concentration.EvenHarmonicFirstMoment

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.EvenHarmonicFirstMoment
open _root_.Reg.Support

noncomputable section

universe u

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ N => firstHarmonicBound N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (N : ℕ) (_ : 0 < N),
    let bound := V.readout () () N
    (∀ {J : Type u} [Fintype J] (w : J → ℝ) (z : J → ℂ),
      (∀ j, 0 ≤ w j) → (∑ j, w j = 1) → (∀ j, ‖z j‖ = 1) →
        (∀ k : ℕ, 0 < k → k < N → ∑ j, (w j : ℂ) * z j ^ (2 * k) = 0) →
          ‖∑ j, (w j : ℂ) * z j‖ ≤ bound) ∧
    (∃ (w : Fin N → ℝ) (z : Fin N → ℂ), (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∀ j, ‖z j‖ = 1) ∧
      (∀ k : ℕ, 0 < k → k < N → ∑ j, (w j : ℂ) * z j ^ (2 * k) = 0) ∧
        ‖∑ j, (w j : ℂ) * z j‖ = bound)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have h := (law 1 (by decide)).1 (fun _ : ULift.{u} (Fin 1) => 1)
    (fun _ => 1) (fun _ => zero_le_one) (by simp) (fun _ => norm_one)
    (fun k hk₀ hk₁ => by omega)
  norm_num [rejected, realize] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 3, ?_⟩
  change firstHarmonicBound 1 ≠ firstHarmonicBound 3
  norm_num [firstHarmonicBound, Real.sin_pi_div_two, Real.sin_pi_div_six]

def evidence : Registration arena.{u} (type_of% @sharp_first_harmonic_even_block.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sharp_first_harmonic_even_block.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sharp_first_harmonic_even_block.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.EvenHarmonicFirstMoment.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.EvenHarmonicFirstMoment.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ caps => firstHarmonicBound caps) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.EvenHarmonicFirstMoment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.EvenHarmonicFirstMoment
