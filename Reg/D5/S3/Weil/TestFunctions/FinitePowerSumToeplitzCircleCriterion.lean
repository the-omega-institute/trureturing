import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Weil.TestFunctions.FinitePowerSumToeplitzCircleCriterion

/-! Source-bound registrations for the power-sum Toeplitz matrix of a finite family closed
under inversion in the unit circle. Each record selects the Toeplitz matrix occurrence of the
original statement, read out from the family, and keeps every other clause verbatim. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.TestFunctions.FinitePowerSumToeplitzCircleCriterion
open _root_.D5.S3.Weil.TestFunctions.LiCurvatureCriterion (toeplitzMatrix)
open Matrix
open scoped ComplexConjugate ComplexOrder

noncomputable section
namespace Reg.D5.S3.Weil.TestFunctions.FinitePowerSumToeplitzCircleCriterion

abbrev Params := Σ _ : ℕ, ℕ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params (fun p => Fin p.1 → ℂ)
    (fun p => Matrix (Fin (p.2 + 1)) (Fin (p.2 + 1)) ℂ)

private theorem toeplitz_dependence :
    toeplitzMatrix (powerSum (![1] : Fin 1 → ℂ)) 1 ≠
      toeplitzMatrix (powerSum (![2] : Fin 1 → ℂ)) 1 := by
  intro he
  have h := congrFun (congrFun he 1) 0
  simp [toeplitzMatrix, powerSum] at h

namespace Circle

def actual : Realization signature :=
  realize signature (fun _ p u => toeplitzMatrix (powerSum u) p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ => (-1 : ℂ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m N : ℕ} (u : Fin m → ℂ) (_ : ∀ j, ‖u j‖ = 1),
    (R.readout () ⟨m, N⟩ u).PosSemidef

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (m := 1) (N := 0) ![1] (fun j => by fin_cases j; simp)
  have hx := hh.dotProduct_mulVec_nonneg (fun _ => 1)
  simp only [rejected, realize] at hx
  have hre := (Complex.le_def.mp hx).1
  simp [dotProduct, mulVec] at hre
  exact absurd hre (not_le.mpr one_pos)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨1, 1⟩, ![1], ![2], toeplitz_dependence⟩

def source : Registration arena (type_of% @powerSum_toeplitz_posSemidef_of_norm_eq_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@powerSum_toeplitz_posSemidef_of_norm_eq_one, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@powerSum_toeplitz_posSemidef_of_norm_eq_one) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Weil.TestFunctions.FinitePowerSumToeplitzCircleCriterion.Circle.unit
  realizationName :=
    `Reg.D5.S3.Weil.TestFunctions.FinitePowerSumToeplitzCircleCriterion.Circle.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p u => toeplitzMatrix (powerSum u) p.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.TestFunctions.FinitePowerSumToeplitzCircleCriterion
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Circle

namespace Criterion

def actual : Realization signature :=
  realize signature (fun _ p u => toeplitzMatrix (powerSum u) p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m N : ℕ} (u : Fin m → ℂ) (_ : (Finset.univ.image u).card ≤ N + 1)
    (_ : ∀ j, u j ≠ 0) (σ : Equiv.Perm (Fin m)) (_ : ∀ j, u (σ j) = (conj (u j))⁻¹),
    (R.readout () ⟨m, N⟩ u).PosSemidef ↔ ∀ j, ‖u j‖ = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hu : ∀ j, (![2, 1 / 2] : Fin 2 → ℂ) j ≠ 0 := by
    intro j
    fin_cases j <;> norm_num
  have hσ : ∀ j, (![2, 1 / 2] : Fin 2 → ℂ) (Equiv.swap 0 1 j) =
      (conj ((![2, 1 / 2] : Fin 2 → ℂ) j))⁻¹ := by
    intro j
    fin_cases j <;> simp [map_ofNat]
  have hcard : (Finset.univ.image (![2, 1 / 2] : Fin 2 → ℂ)).card ≤ 1 + 1 :=
    Finset.card_image_le.trans (by simp)
  have hh := (h (m := 2) (N := 1) ![2, 1 / 2] hcard hu (Equiv.swap 0 1) hσ).mp
  simp only [rejected, realize] at hh
  have h0 := hh Matrix.PosSemidef.zero 0
  norm_num at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨1, 1⟩, ![1], ![2], toeplitz_dependence⟩

def source : Registration arena (type_of% @toeplitz_posSemidef_iff_norm_eq_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@toeplitz_posSemidef_iff_norm_eq_one, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@toeplitz_posSemidef_iff_norm_eq_one) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Weil.TestFunctions.FinitePowerSumToeplitzCircleCriterion.Criterion.unit
  realizationName :=
    `Reg.D5.S3.Weil.TestFunctions.FinitePowerSumToeplitzCircleCriterion.Criterion.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p u => toeplitzMatrix (powerSum u) p.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.TestFunctions.FinitePowerSumToeplitzCircleCriterion
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Criterion

end Reg.D5.S3.Weil.TestFunctions.FinitePowerSumToeplitzCircleCriterion
