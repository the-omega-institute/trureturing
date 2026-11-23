import Reg.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
import D5.S3.Fourier.Concentration.PerturbedHarmonicWeights

/-! The upper cutoff observes the perturbed ordinate at each coordinate. -/

namespace Reg.D5.S3.Fourier.Concentration.PerturbedHarmonicWeights

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.PerturbedHarmonicWeights
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (diagonal)
open FiniteSpectralPerturbation (actual frequencyEvidence frequencySignature)
open FiniteSineMissingWindow (sensitivity)
open LeanInformationAudit Finset

noncomputable section

universe u

private def rejected : Realization frequencySignature.{u} :=
  realize frequencySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev cutoffArena : Arena where
  signature := frequencySignature.{u}
  Law A := ∀ {J : Type u} [DecidableEq J]
    (V : Finset J) (g g' radius : J → ℝ) {a R X T η : ℝ}
    (_ : 0 ≤ a) (_ : ∀ j, radius j ≤ R) (_ : ∀ j, |g' j - g j| ≤ radius j)
    (_ : ∀ j : V, radius j < g j)
    (_ : ∀ j, X - R < g j → g j ≤ T + R → j ∈ V)
    (p : ℕ) (_ : 0 ≤ η),
    (∀ j, X < g' j → A.readout () ⟨J, g'⟩ j ≤ T → j ∈ V) ∧
    let s := (univ : Finset V).filter (fun j : V => X < g' j ∧ g' j ≤ T)
    let u : s → ℝ := fun j => g' j.val / (a + (g' j.val) ^ 2)
    let v : V → ℝ := fun j => (g j / (g j - radius j)) * (g j / (a + (g j) ^ 2))
    tailCollisionMass (fun j : s => g' j.val) u p η - diagonal u p ≤
      tailCollisionMass (fun j : V => g' j) v p η - diagonal v p

private theorem rejected_law : ¬ cutoffArena.{u}.Law rejected := by
  intro law
  have h := law (J := ULift.{u} Unit) ∅ (fun _ => 2) (fun _ => 2) 0
    (a := 0) (R := 0) (X := 1) (T := 1) (η := 0) le_rfl (by simp) (by simp)
    (by simp) (by norm_num) 0 le_rfl
  have hmem := h.1 (ULift.up ()) (by norm_num) (by change (0 : ℝ) ≤ 1; norm_num)
  simp at hmem

def cutoffEvidence :
    Registration cutoffArena.{u} (type_of% @collision_excess_le_on_perturbed_cutoff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@collision_excess_le_on_perturbed_cutoff.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity cutoffArena.Law actual rejected rejected_law
  dependence := frequencyEvidence.{u}.dependence

def cutoffRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@collision_excess_le_on_perturbed_cutoff.{u})
      (Realization frequencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.PerturbedHarmonicWeights.cutoffUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.PerturbedHarmonicWeights.cutoffEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨cutoffArena.{u}⟩
  objectArena := .source ⟨cutoffArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cutoffArena.{u} ⟨cutoffEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.PerturbedHarmonicWeights
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms cutoffRegistration

end

end Reg.D5.S3.Fourier.Concentration.PerturbedHarmonicWeights
