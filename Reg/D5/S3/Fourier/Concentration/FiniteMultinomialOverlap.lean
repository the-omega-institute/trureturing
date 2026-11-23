import Reg.D5.S3.Fourier.Concentration.FiniteSineMissingWindow
import D5.S3.Fourier.Concentration.FiniteMultinomialOverlap

/-! Total weight and squared frequency scale in the finite overlap estimates. -/

namespace Reg.D5.S3.Fourier.Concentration.FiniteMultinomialOverlap

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteMultinomialOverlap
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight diagonal)
open FiniteSineMissingWindow (oneRole sensitivity)
open LeanInformationAudit Finset

noncomputable section

universe u

abbrev weightSignature : Signature :=
  oneRole (Σ J : Type u, Fintype J) (fun q => q.1 → ℝ)

private def weightReadout : Realization weightSignature.{u} :=
  realize weightSignature (fun _ q w => let _ := q.2; ∑ j, w j) (fun e => nomatch e)

private def zeroWeightReadout : Realization weightSignature.{u} :=
  realize weightSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev weightArena : Arena where
  signature := weightSignature.{u}
  Law A := ∀ {J : Type u} [i : Fintype J] [DecidableEq J]
    (w : J → ℝ) (_ : ∀ j, 0 ≤ w j) (p k : ℕ) (_ : k ≤ p),
    (∑ m ∈ piAntidiag univ p, ∑ n ∈ piAntidiag univ p,
      if k ≤ ∑ j, min (m j) (n j) then monomialWeight w m * monomialWeight w n else 0) ≤
      (Nat.choose p k : ℝ) ^ 2 * (A.readout () ⟨J, i⟩ w) ^ (2 * (p - k)) * diagonal w k

private theorem zeroWeight_fails : ¬ weightArena.{u}.Law zeroWeightReadout := by
  intro law
  have h := law (J := ULift.{u} Unit) (fun _ => 1) (by simp) 1 0 (by simp)
  have hsum :
      (∑ m ∈ piAntidiag (univ : Finset (ULift.{u} Unit)) 1,
        monomialWeight (fun _ => (1 : ℝ)) m) = 1 := by
    unfold monomialWeight
    rw [← sum_pow_eq_sum_piAntidiag]
    simp
  simp only [zero_le, ↓reduceIte, ← mul_sum, hsum, mul_one] at h
  norm_num [zeroWeightReadout, realize] at h

private theorem weight_dependence : ObservationalDependence weightSignature.{u} weightReadout := by
  intro _
  refine ⟨⟨ULift.{u} Unit, inferInstance⟩, 0, 1, ?_⟩
  change (∑ _ : ULift.{u} Unit, (0 : ℝ)) ≠ ∑ _ : ULift.{u} Unit, (1 : ℝ)
  simp

def weightEvidence :
    Registration weightArena.{u} (type_of% @weighted_overlap_le_diagonal.{u}) where
  actual := weightReadout
  bridge := Iff.rfl
  variation := ⟨@weighted_overlap_le_diagonal.{u}, zeroWeightReadout, zeroWeight_fails⟩
  sensitivity := sensitivity weightArena.Law weightReadout zeroWeightReadout zeroWeight_fails
  dependence := weight_dependence

def weightRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weighted_overlap_le_diagonal.{u}) (Realization weightSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FiniteMultinomialOverlap.weightUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FiniteMultinomialOverlap.weightEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨weightArena.{u}⟩
  objectArena := .source ⟨weightArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightArena.{u} ⟨weightEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ q w => let _ := q.2; ∑ j, w j)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FiniteMultinomialOverlap
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev scaleSignature : Signature :=
  oneRole (Σ J : Type u, Σ _ : Fintype J, (J → ℕ) × (J → ℕ)) (fun q => q.1 → ℝ)

private def scaleReadout : Realization scaleSignature.{u} :=
  realize scaleSignature
    (fun _ q r => let _ := q.2.1; ∑ j, (((q.2.2.1 j : ℝ) - q.2.2.2 j) * r j) ^ 2)
    (fun e => nomatch e)

private def zeroScaleReadout : Realization scaleSignature.{u} :=
  realize scaleSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev scaleArena : Arena where
  signature := scaleSignature.{u}
  Law A := ∀ {J : Type u} [i : Fintype J] (r : J → ℝ) {ρ : ℝ}
    (_ : 0 ≤ ρ) (_ : ∀ j, ρ ≤ r j) (m n : J → ℕ) (p : ℕ)
    (_ : (∑ j, m j) = p) (_ : (∑ j, n j) = p),
    2 * ρ ^ 2 * ((p : ℝ) - ∑ j, (min (m j) (n j) : ℝ)) ≤ A.readout () ⟨J, i, m, n⟩ r

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
  rw [sum_liftBool] at h
  norm_num [leftCount, rightCount, zeroScaleReadout, realize] at h

private theorem scale_dependence : ObservationalDependence scaleSignature.{u} scaleReadout := by
  intro _
  refine ⟨⟨ULift.{u} Bool, inferInstance, leftCount, rightCount⟩, 0, 1, ?_⟩
  change (∑ j : ULift.{u} Bool, (((leftCount j : ℝ) - rightCount j) * 0) ^ 2) ≠
    ∑ j : ULift.{u} Bool, (((leftCount j : ℝ) - rightCount j) * 1) ^ 2
  simp only [sum_liftBool]
  norm_num [leftCount, rightCount]

def scaleEvidence :
    Registration scaleArena.{u} (type_of% @weighted_count_difference_sq_ge.{u}) where
  actual := scaleReadout
  bridge := Iff.rfl
  variation := ⟨@weighted_count_difference_sq_ge.{u}, zeroScaleReadout, zeroScale_fails⟩
  sensitivity := sensitivity scaleArena.Law scaleReadout zeroScaleReadout zeroScale_fails
  dependence := scale_dependence

def scaleRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weighted_count_difference_sq_ge.{u}) (Realization scaleSignature.{u}) Unit Unit where
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
  readout := some (realize scaleSignature
    (fun _ q r => let _ := q.2.1; ∑ j, (((q.2.2.1 j : ℝ) - q.2.2.2 j) * r j) ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FiniteMultinomialOverlap
    definition := none
    coordinates := #[0, 1, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms weightRegistration
#print axioms scaleRegistration

end

end Reg.D5.S3.Fourier.Concentration.FiniteMultinomialOverlap
