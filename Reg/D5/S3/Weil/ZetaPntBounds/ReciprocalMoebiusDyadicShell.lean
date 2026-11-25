import D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusDyadicShell
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The dyadic obstruction observes the shell mass as a function of the cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusDyadicShell

open MeasureTheory Set LeanInformationAudit
open _root_.D5.S3.Arith.MoebiusLogarithmic (reciprocalSum)
open _root_.D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse
  (dyadicReciprocalMoebiusShell_lower)
open _root_.D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
  (zetaZeroData zetaZeroData_isNontrivial)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ P =>
    1 + ∫ u in (1 : ℝ)..P, |reciprocalSum u - reciprocalSum (u / 2)|)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P : ℝ}, 1 ≤ P → ∀ {rho : ℂ},
    0 < rho.re → rho.re < 1 → riemannZeta rho = 0 →
    rho.re * ‖1 - (2 : ℂ) ^ (1 - rho)‖ ^ (2 : ℕ) / ‖rho * (rho - 1)‖ * P ^ rho.re ≤
      R.readout () () P

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨hz, h₀, h₁⟩ := zetaZeroData_isNontrivial 0
  have hbad := h (P := 1) le_rfl h₀ h₁ hz
  change _ ≤ (-1 : ℝ) at hbad
  have hnonneg : 0 ≤ (zetaZeroData.zero 0).re *
      ‖1 - (2 : ℂ) ^ (1 - zetaZeroData.zero 0)‖ ^ (2 : ℕ) /
      ‖zetaZeroData.zero 0 * (zetaZeroData.zero 0 - 1)‖ *
      (1 : ℝ) ^ (zetaZeroData.zero 0).re := by positivity
  linarith

private theorem mass_at_two :
    (∫ u in (1 : ℝ)..2, |reciprocalSum u - reciprocalSum (u / 2)|) = 1 := by
  calc
    _ = ∫ _ in (1 : ℝ)..2, (1 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro u hu
      have hfloor : Nat.floor u = 1 := (Nat.floor_eq_iff (by linarith [hu.1])).2 (by
        norm_num
        exact ⟨hu.1.le, hu.2⟩)
      have hhalf : Nat.floor (u / 2) = 0 := Nat.floor_eq_zero.2 (by linarith [hu.2])
      simp [reciprocalSum, hfloor, hhalf, ArithmeticFunction.moebius_apply_one]
    _ = 1 := by norm_num [intervalIntegral.integral_const]

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 1, 2, ?_⟩
  change (1 + ∫ u in (1 : ℝ)..1, |reciprocalSum u - reciprocalSum (u / 2)|) ≠
    (1 + ∫ u in (1 : ℝ)..2, |reciprocalSum u - reciprocalSum (u / 2)|)
  rw [mass_at_two, intervalIntegral.integral_same]
  norm_num

def family : Registration arena (type_of% @dyadicReciprocalMoebiusShell_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@dyadicReciprocalMoebiusShell_lower, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dyadicReciprocalMoebiusShell_lower) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusFloorInverse.dyadicReciprocalMoebiusShell_lower.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusDyadicShell.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P =>
    1 + ∫ u in (1 : ℝ)..P, |reciprocalSum u - reciprocalSum (u / 2)|)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusDyadicShell
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaPntBounds.ReciprocalMoebiusDyadicShell
