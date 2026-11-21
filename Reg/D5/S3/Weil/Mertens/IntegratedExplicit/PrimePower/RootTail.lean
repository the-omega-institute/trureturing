import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootTail
import Reg.Support.SingleDependentReadout

/-! Source audits of the Chebyshev readout at the root cutoffs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootTail

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => Chebyshev.psi t) (fun e => nomatch e)

private def shifted (c : ℝ) : Realization signature :=
  realize signature (fun _ _ t => Chebyshev.psi t + c) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 1, ?_⟩
  change Chebyshev.psi 2 ≠ Chebyshev.psi 1
  rw [Chebyshev.psi_one, ne_eq, Chebyshev.psi_eq_zero_iff]
  norm_num

private theorem power_kernel {p : ℝ} (hp : p < 1) :
    IntegrableOn (fun t : ℝ => t ^ p / t ^ (2 : ℕ)) (Ioi 1) := by
  apply (integrableOn_Ioi_rpow_of_lt (a := p - 2) (by linarith) zero_lt_one).congr_fun
    (fun t ht => ?_) measurableSet_Ioi
  rw [Real.rpow_sub (zero_lt_one.trans ht), Real.rpow_two]

private theorem psi_kernel {p : ℝ} (hp : p < 1) :
    IntegrableOn (fun t : ℝ => Chebyshev.psi (t ^ p) / t ^ 2) (Ioi 1) := by
  apply ((power_kernel hp).const_mul (Real.log 4 + 4)).mono'
  · exact ((Chebyshev.psi_mono.measurable.comp (by fun_prop)).div
      (measurable_id.pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖Chebyshev.psi (t ^ p) / t ^ 2‖ ≤ (Real.log 4 + 4) * (t ^ p / t ^ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Chebyshev.psi_nonneg _) (sq_nonneg _)),
      ← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg (zero_lt_one.trans ht).le _)) (sq_nonneg _)

private theorem integral_shift {f : ℝ → ℝ}
    (hf : IntegrableOn (fun t => f t / t ^ (2 : ℕ)) (Ioi 1)) (c : ℝ) :
    (∫ t in Ioi (1 : ℝ), (f t + c) / t ^ (2 : ℕ)) =
      (∫ t in Ioi (1 : ℝ), f t / t ^ (2 : ℕ)) + c := by
  have hi := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) zero_lt_one
  have he (t : ℝ) (ht : t ∈ Ioi (1 : ℝ)) :
      (f t + c) / t ^ (2 : ℕ) = f t / t ^ (2 : ℕ) + c * t ^ (-2 : ℝ) := by
    rw [add_div, Real.rpow_neg (zero_lt_one.trans ht).le, Real.rpow_two, div_eq_mul_inv c]
  rw [setIntegral_congr_fun measurableSet_Ioi he,
    integral_add hf (hi.const_mul c), integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
  norm_num

namespace Centered

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r x : ℝ} (_hr : 1 ≤ r) (_hx : 0 < x),
    let y := x ^ r⁻¹
    Real.sqrt x * (∫ t in Ioi x, (R.readout () () (t ^ r⁻¹) - t ^ r⁻¹) / t ^ 2) =
      r * Real.sqrt x *
        (Q y * y ^ (1 - r) - (r - 1) * (∫ s in Ioi y, s ^ (-r) * Q s))

theorem source_reconstruction : (type_of% @centered_root_tail) ↔ arena.Law actual := Iff.rfl

theorem rejected_law : ¬ arena.Law (shifted 1) := by
  intro h
  have hp : (2 : ℝ)⁻¹ < 1 := by norm_num
  have hi : IntegrableOn (fun t : ℝ =>
      (Chebyshev.psi (t ^ (2 : ℝ)⁻¹) - t ^ (2 : ℝ)⁻¹) / t ^ (2 : ℕ)) (Ioi 1) := by
    simpa only [sub_div, Pi.sub_def] using (psi_kernel hp).sub (power_kernel hp)
  have hbad := h (r := 2) (x := 1) (by norm_num) zero_lt_one
  have hactual := centered_root_tail (r := 2) (x := 1) (by norm_num) zero_lt_one
  change Real.sqrt 1 * (∫ t in Ioi (1 : ℝ),
    (Chebyshev.psi (t ^ (2 : ℝ)⁻¹) + 1 - t ^ (2 : ℝ)⁻¹) / t ^ 2) = _ at hbad
  have he (t : ℝ) : Chebyshev.psi (t ^ (2 : ℝ)⁻¹) + 1 - t ^ (2 : ℝ)⁻¹ =
      (Chebyshev.psi (t ^ (2 : ℝ)⁻¹) - t ^ (2 : ℝ)⁻¹) + 1 := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => by rw [he]), integral_shift hi] at hbad
  dsimp only at hactual hbad
  simp only [Real.sqrt_one, one_mul] at hactual hbad
  linarith only [hactual, hbad]

def family : Registration arena (type_of% @centered_root_tail) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@centered_root_tail, shifted 1, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual
    (shifted 1) rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@centered_root_tail) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.centered_root_tail.__information_unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootTail.Centered.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => Chebyshev.psi t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg",
        "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Centered

namespace Main

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r x : ℝ} (_hr : 1 < r) (_hx : 0 < x),
    Real.sqrt x * (∫ t in Ioi x, R.readout () () (t ^ r⁻¹) / t ^ 2) =
      r / (r - 1) * x ^ (r⁻¹ - 1 / 2) +
        Real.sqrt x * (∫ t in Ioi x, (Chebyshev.psi (t ^ r⁻¹) - t ^ r⁻¹) / t ^ 2)

theorem source_reconstruction : (type_of% @root_tail_main) ↔ arena.Law actual := Iff.rfl

theorem rejected_law : ¬ arena.Law (shifted 1) := by
  intro h
  have hbad := h (r := 2) (x := 1) (by norm_num) zero_lt_one
  have hactual := root_tail_main (r := 2) (x := 1) (by norm_num) zero_lt_one
  change Real.sqrt 1 * (∫ t in Ioi (1 : ℝ),
    (Chebyshev.psi (t ^ (2 : ℝ)⁻¹) + 1) / t ^ 2) = _ at hbad
  rw [integral_shift (psi_kernel (show (2 : ℝ)⁻¹ < 1 by norm_num))] at hbad
  simp only [Real.sqrt_one, one_mul] at hactual hbad
  linarith only [hactual, hbad]

def family : Registration arena (type_of% @root_tail_main) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@root_tail_main, shifted 1, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual
    (shifted 1) rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@root_tail_main) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.root_tail_main.__information_unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootTail.Main.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => Chebyshev.psi t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Main

namespace Remainder

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ} (_hx : 0 < x),
    let E := Q x - primeTail x -
      (∫ t in Ioi x, R.readout () () (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
      (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2)
    0 ≤ E ∧ Real.sqrt x * E ≤ (Real.log 4 + 4) * (5 / 4) * x ^ (-(3 / 10) : ℝ)

theorem source_reconstruction : (type_of% @root_cutoff_remainder) ↔ arena.Law actual := Iff.rfl

private def excessAtOne : ℝ := Q 1 - primeTail 1 -
  (∫ t in Ioi (1 : ℝ), Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
  (∫ t in Ioi (1 : ℝ), Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2) + 1

theorem rejected_law : ¬ arena.Law (shifted excessAtOne) := by
  intro h
  have hbad := (h (x := 1) zero_lt_one).1
  change 0 ≤ Q 1 - primeTail 1 -
    (∫ t in Ioi (1 : ℝ), (Chebyshev.psi (t ^ (2 : ℝ)⁻¹) + excessAtOne) / t ^ 2) -
    (∫ t in Ioi (1 : ℝ), Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2) at hbad
  rw [integral_shift (psi_kernel (show (2 : ℝ)⁻¹ < 1 by norm_num))] at hbad
  unfold excessAtOne at hbad
  linarith only [hbad]

def family : Registration arena (type_of% @root_cutoff_remainder) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@root_cutoff_remainder, shifted excessAtOne, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual
    (shifted excessAtOne) rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@root_cutoff_remainder) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.root_cutoff_remainder.__information_unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootTail.Remainder.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => Chebyshev.psi t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value", "fn", "arg", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Remainder

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootTail
