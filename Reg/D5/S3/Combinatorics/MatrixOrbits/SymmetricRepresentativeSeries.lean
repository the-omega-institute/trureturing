import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.MatrixOrbits.SymmetricRepresentativeSeries
import Reg.Support.SingleDependentReadout

/-! The all-degree coefficient observation for symmetric-representative orbits. -/

namespace Reg.D5.S3.Combinatorics.MatrixOrbits.SymmetricRepresentativeSeries

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.A333886
open LeanInformationAudit
open PowerSeries


noncomputable section

private abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ n => coeff n publishedSeries) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    (Nat.card {ω : Orbit n // ∃ B : Margin n,
      Quotient.mk _ B = ω ∧ ∀ i j : Fin 4, B.val i j = B.val j i} : ℚ) =
      R.readout () () n

private theorem coeff_zero : coeff 0 publishedSeries = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply]
  simp [publishedSeries, publishedNumerator, constantCoeff_invOfUnit]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0
  change _ = (0 : ℚ) at h0
  have he := source_identity_literal 0
  rw [h0, coeff_zero] at he
  exact zero_ne_one he

private theorem coeff_two : coeff 2 publishedSeries = 5 := by
  have ant1 : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  have ant2 : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
  have hd0 : coeff 0 publishedDenominator = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply]
    simp [publishedDenominator]
  have hd1 : coeff 1 publishedDenominator = -3 := by
    unfold publishedDenominator
    norm_num [pow_succ, coeff_mul, ant1, Finset.Nat.antidiagonal_zero, coeff_X, coeff_one]
  have hd2 : coeff 2 publishedDenominator = 2 := by
    unfold publishedDenominator
    norm_num [pow_succ, coeff_mul, ant1, ant2, Finset.Nat.antidiagonal_zero, coeff_X, coeff_one]
  have h1 := congrArg (coeff 1) clearPublished
  simp only [coeff_mul, ant1, Finset.sum_insert (by decide : (0, 1) ∉ ({(1, 0)} : Finset (ℕ × ℕ))),
    Finset.sum_singleton, hd0, hd1, coeff_zero, one_mul, mul_one] at h1
  have hn1 : coeff 1 publishedNumerator = -2 := by
    norm_num [publishedNumerator, coeff_X, coeff_X_pow, coeff_one,
      ← map_ofNat PowerSeries.C, coeff_C_mul]
  rw [hn1] at h1
  have hc1 : coeff 1 publishedSeries = 1 := by linarith
  have h2 := congrArg (coeff 2) clearPublished
  simp only [coeff_mul, ant2,
    Finset.sum_insert (by decide : (0, 2) ∉ ({(1, 1), (2, 0)} : Finset (ℕ × ℕ))),
    Finset.sum_insert (by decide : (1, 1) ∉ ({(2, 0)} : Finset (ℕ × ℕ))),
    Finset.sum_singleton, hd0, hd1, hd2, coeff_zero, hc1, one_mul, mul_one] at h2
  have hn2 : coeff 2 publishedNumerator = 4 := by
    norm_num [publishedNumerator, coeff_X, coeff_X_pow, coeff_one,
      ← map_ofNat PowerSeries.C, coeff_C_mul]
  rw [hn2] at h2
  linarith

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 2, ?_⟩
  change coeff 0 publishedSeries ≠ coeff 2 publishedSeries
  rw [coeff_zero, coeff_two]
  norm_num

def family : Registration arena (type_of% @source_identity_literal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@source_identity_literal, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@source_identity_literal) (Realization signature) Unit Unit where
  unitName := `A333886.source_identity_literal.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => coeff n publishedSeries) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.SymmetricRepresentativeSeries
    definition := none

    coordinates := #[]
    readouts := #[{ path := #["body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace ClearingDenominator

private abbrev signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => PowerSeries ℚ) (fun _ => PowerSeries ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ S => publishedDenominator * S) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () publishedSeries = publishedNumerator

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn : (0 : PowerSeries ℚ) = publishedNumerator := h
  have he := congrArg (constantCoeff (R := ℚ)) hn
  norm_num [publishedNumerator] at he

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, publishedSeries, ?_⟩
  change publishedDenominator * 0 ≠ publishedDenominator * publishedSeries
  rw [mul_zero, clearPublished]
  intro he
  have hz := congrArg (constantCoeff (R := ℚ)) he
  norm_num [publishedNumerator] at hz

def family : Registration arena (type_of% @clearPublished) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@clearPublished, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@clearPublished) (Realization signature) Unit Unit where
  unitName := `A333886.clearPublished.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => publishedDenominator * S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.SymmetricRepresentativeSeries
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ClearingDenominator

end
end Reg.D5.S3.Combinatorics.MatrixOrbits.SymmetricRepresentativeSeries
