import Reg.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
import D5.S3.Fourier.Concentration.FiniteMultinomialOverlap

/-! Pointwise radius evaluation in the squared frequency scale. -/

namespace Reg.D5.S3.Fourier.Concentration.FiniteMultinomialOverlap

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteMultinomialOverlap
open FiniteSineMissingWindow (sensitivity)
open FiniteSpectralPerturbation (frequencySignature actual)
open LeanInformationAudit Finset

noncomputable section

universe u

private def zeroScaleReadout : Realization frequencySignature.{u} :=
  realize frequencySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev scaleArena : Arena where
  signature := frequencySignature.{u}
  Law A := ∀ {J : Type u} [Fintype J] (r : J → ℝ) {ρ : ℝ}
    (_ : 0 ≤ ρ) (_ : ∀ j, ρ ≤ r j) (m n : J → ℕ) (p : ℕ)
    (_ : (∑ j, m j) = p) (_ : (∑ j, n j) = p),
    2 * ρ ^ 2 * ((p : ℝ) - ∑ j, (min (m j) (n j) : ℝ)) ≤
      ∑ j, (((m j : ℝ) - n j) * A.readout () ⟨J, r⟩ j) ^ 2

private theorem liftBool_univ :
    (univ : Finset (ULift.{u} Bool)) = {ULift.up false, ULift.up true} := by
  ext x
  rcases x with ⟨b⟩
  cases b <;> simp

private def leftCount (j : ULift.{u} Bool) : ℕ := if j.down then 0 else 1

private def rightCount (j : ULift.{u} Bool) : ℕ := if j.down then 1 else 0

private theorem sum_liftBool {A : Type*} [AddCommMonoid A] (f : ULift.{u} Bool → A) :
    (∑ j, f j) = f (ULift.up false) + f (ULift.up true) := by
  rw [liftBool_univ, sum_insert (by decide), sum_singleton]

private theorem zeroScale_fails : ¬ scaleArena.{u}.Law zeroScaleReadout := by
  intro law
  have h := law (J := ULift.{u} Bool) 1 (ρ := 1) zero_le_one (fun _ => le_rfl)
    leftCount rightCount 1 (by rw [sum_liftBool]; rfl) (by rw [sum_liftBool]; rfl)
  simp only [sum_liftBool] at h
  norm_num [leftCount, rightCount, zeroScaleReadout, realize] at h

def scaleEvidence :
    Registration scaleArena.{u} (type_of% @weighted_count_difference_sq_ge.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_count_difference_sq_ge.{u}, zeroScaleReadout, zeroScale_fails⟩
  sensitivity := sensitivity scaleArena.Law actual zeroScaleReadout zeroScale_fails
  dependence := (FiniteSpectralPerturbation.frequencyEvidence.{u}).dependence

def scaleRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weighted_count_difference_sq_ge.{u}) (Realization frequencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FiniteMultinomialOverlap.scaleUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FiniteMultinomialOverlap.scaleEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨scaleArena.{u}⟩
  objectArena := .source ⟨scaleArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source scaleArena.{u} ⟨scaleEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FiniteMultinomialOverlap
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms scaleRegistration

end

end Reg.D5.S3.Fourier.Concentration.FiniteMultinomialOverlap
