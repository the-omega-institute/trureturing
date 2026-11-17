import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.ZeroAbscissaMertensLowerBound
import Reg.Support.SingleDependentReadout

/-! Source-bound audit readout for the unconditional zero-abscissa lower power law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.ZeroAbscissaMertensLowerBound
open _root_.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (B)
open _root_.D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa)
open _root_.D5.S3.Weil.Mertens.ZeroAbscissaPower
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open Filter
open scoped Topology

namespace Reg.D5.S3.Arith.Robin.Analytic.ZeroAbscissaMertensLowerBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => B x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => -(x ^ (3 : ℕ))) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ ε : ℝ, 0 < ε → ∃ C T : ℝ,
    0 ≤ C ∧ 2 ≤ T ∧ ∀ x : ℝ, T ≤ x →
      -C * Real.rpow x (zeroAbscissa - 1 + ε) ≤ V.readout () () x

private theorem zeroAbscissa_le_one : zeroAbscissa ≤ 1 := by
  apply csSup_le (show (Complex.re '' {ρ : ℂ |
    _root_.D5.S3.Weil.ZeroSum.IsNontrivialZero ρ}).Nonempty from
    ⟨(actualZero 0).re, actualZero 0,
      actualData.zero_isNontrivial (actualOccurrenceEquiv 0).1, rfl⟩)
  rintro r ⟨ρ, hρ, rfl⟩
  exact hρ.2.2.le

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨C, T, hC, hT, hbound⟩ := h (2 - zeroAbscissa) (by linarith [zeroAbscissa_le_one])
  let x : ℝ := max T (max |C| 2) + 1
  have hxT : T ≤ x := by
    dsimp only [x]
    linarith [le_max_left T (max |C| 2)]
  have hx2 : 2 ≤ x := by
    dsimp only [x]
    linarith [le_max_right T (max |C| 2), le_max_right |C| 2]
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxC : C < x := by
    dsimp only [x]
    have hmax : |C| ≤ max T (max |C| 2) :=
      (le_max_left |C| 2).trans (le_max_right T (max |C| 2))
    linarith [le_abs_self C]
  have hh := hbound x hxT
  change -C * Real.rpow x (zeroAbscissa - 1 + (2 - zeroAbscissa)) ≤
    -(x ^ (3 : ℕ)) at hh
  rw [show zeroAbscissa - 1 + (2 - zeroAbscissa) = 1 by ring,
    Real.rpow_eq_pow, Real.rpow_one] at hh
  have hmul : C * x < x * x := mul_lt_mul_of_pos_right hxC hx0
  have hpow : x * x ≤ x ^ (3 : ℕ) := by
    nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx1)]
  nlinarith [hh]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _i
  refine ⟨(), 0, 2, ?_⟩
  change B 0 ≠ B 2
  have hzero : B 0 = Real.eulerMascheroniConstant := by
    simp [B, Mertens.E₃]
  have htwo : B 2 = Real.log (1 / 2 : ℝ) +
      Real.eulerMascheroniConstant + Real.log (Real.log (Real.log 2)) := by
    norm_num [B, Mertens.E₃, Chebyshev.theta,
      show Finset.Ioc 0 2 = {1, 2} by decide, Finset.sum_filter]
    ring
  have hlpos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hllt : Real.log (2 : ℝ) < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hllneg : Real.log (Real.log (2 : ℝ)) < 0 := Real.log_neg hlpos hllt
  have hllgt : -1 < Real.log (Real.log (2 : ℝ)) := by
    have hlo := Real.one_sub_inv_le_log_of_pos hlpos
    have hhalf : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      norm_num at this
      linarith
    have hinv : (Real.log (2 : ℝ))⁻¹ < 2 := by
      apply (inv_lt_iff_one_lt_mul₀ hlpos).mpr
      linarith
    linarith
  have houter : Real.log (Real.log (Real.log (2 : ℝ))) < 0 := by
    rw [← Real.log_neg_eq_log (Real.log (Real.log (2 : ℝ)))]
    exact Real.log_neg (by linarith) (by linarith)
  have hhalfneg : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  rw [hzero, htwo]
  linarith

def family : Registration arena (type_of% @actual_B_zero_abscissa_lower_power) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_B_zero_abscissa_lower_power, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_B_zero_abscissa_lower_power) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.Robin.Analytic.ZeroAbscissaMertensLowerBound.actual_B_zero_abscissa_lower_power.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Robin.Analytic.ZeroAbscissaMertensLowerBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.ZeroAbscissaMertensLowerBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg",
        "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms actual_B_zero_abscissa_lower_power
#print axioms family
#print axioms registration

end Reg.D5.S3.Arith.Robin.Analytic.ZeroAbscissaMertensLowerBound
