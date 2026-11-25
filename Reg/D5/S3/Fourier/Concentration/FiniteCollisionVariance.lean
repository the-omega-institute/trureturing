import Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow
import D5.S3.Fourier.Concentration.FiniteCollisionVariance

/-! The total input weight in the finite-resolution collision inequality. -/

namespace Reg.D5.S3.Fourier.Concentration.FiniteCollisionVariance

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteCollisionVariance
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open FiniteSineMissingWindow (oneRole sensitivity)
open LeanInformationAudit Finset

noncomputable section

universe u

abbrev weightSignature : Signature :=
  oneRole (Σ J : Type u, Fintype J) (fun q => q.1 → ℝ)

def actual : Realization weightSignature.{u} :=
  realize weightSignature
    (fun _ q w => @Finset.sum q.1 ℝ _ (@Finset.univ q.1 q.2) w)
    (fun e => nomatch e)

private def rejected : Realization weightSignature.{u} :=
  realize weightSignature (fun _ _ _ => 4) (fun e => nomatch e)

abbrev weightArena : Arena where
  signature := weightSignature.{u}
  Law V := ∀ {J : Type u} [i : Fintype J] [DecidableEq J]
    (g w : J → ℝ) (_ : ∀ j, 0 ≤ w j) (_ : 0 < ∑ j, w j) {p : ℕ} (_ : 0 < p)
    {η : ℝ} (_ : 0 < η),
    let W := V.readout () ⟨J, i⟩ w
    let μ := (∑ j, w j * g j) / W
    let variance := (∑ j, w j * (g j - μ) ^ 2) / W
    (9 / 16 : ℝ) * W ^ (2 * p) ≤
      (1 + 4 * Real.sqrt ((p : ℝ) * variance) / η) * tailCollisionMass g w p η

private theorem unit_collision :
    tailCollisionMass (J := ULift.{u} Unit) 0 1 1 1 = 1 := by
  have hu : (univ : Finset (ULift.{u} Unit)) = {ULift.up ()} := by
    ext j
    rcases j with ⟨⟨⟩⟩
    simp
  have h : piAntidiag (univ : Finset (ULift.{u} Unit)) 1 = {fun _ => 1} := by
    ext m
    simp only [mem_piAntidiag, mem_univ, not_true_eq_false, false_implies, implies_true,
      and_true, mem_singleton, hu, sum_singleton]
    constructor
    · intro hm
      funext j
      rcases j with ⟨⟨⟩⟩
      exact hm
    · rintro rfl
      rfl
  unfold tailCollisionMass nearCollisionMass
  rw [h]
  simp only [sum_singleton, monomialFrequency, Pi.zero_apply, mul_zero, sum_const_zero,
    sub_self, abs_zero, zero_le_one, if_true]
  norm_num [monomialWeight, Nat.multinomial, hu]

private theorem rejected_law : ¬ weightArena.{u}.Law rejected := by
  intro law
  have h := law (J := ULift.{u} Unit) 0 1 (by simp) (by simp)
    (p := 1) Nat.one_pos (η := 1) zero_lt_one
  simp [rejected, realize, unit_collision] at h
  norm_num at h

private theorem weight_dependence : ObservationalDependence weightSignature.{u} actual := by
  intro _
  refine ⟨⟨ULift.{u} Unit, inferInstance⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change (∑ _ : ULift.{u} Unit, (0 : ℝ)) ≠ ∑ _ : ULift.{u} Unit, (1 : ℝ)
  simp

def weightEvidence :
    Registration weightArena.{u} (type_of% @tailCollisionMass_lower_variance.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tailCollisionMass_lower_variance.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity weightArena.Law actual rejected rejected_law
  dependence := weight_dependence

def weightRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@tailCollisionMass_lower_variance.{u}) (Realization weightSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FiniteCollisionVariance.weightUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FiniteCollisionVariance.weightEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨weightArena.{u}⟩
  objectArena := .source ⟨weightArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightArena.{u} ⟨weightEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature
    (fun _ q w => @Finset.sum q.1 ℝ _ (@Finset.univ q.1 q.2) w)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FiniteCollisionVariance
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "value"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms weightRegistration

end

end Reg.D5.S3.Fourier.Concentration.FiniteCollisionVariance
