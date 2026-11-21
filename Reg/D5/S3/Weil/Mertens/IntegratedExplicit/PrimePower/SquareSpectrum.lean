import Mathlib.Analysis.Normed.Group.Tannery
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SquareSpectrum
import Reg.Support.SingleDependentReadout

/-! Source audits of the zero-tail normalization and the square-cutoff density. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit MeasureTheory Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SquareSpectrum

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ u => zeroTail u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ u : ℝ, R.readout () () u = (Real.exp (-u) : ℂ) * actualH u

theorem source_reconstruction : (type_of% @zeroTail_eq) ↔ arena.Law actual := Iff.rfl

private theorem actualH_at_zero : actualH 0 = (firstLiMass : ℂ) := by
  simpa [actualH] using actualCoeff_hasSum.tsum_eq

private theorem zeroTail_at_zero_ne : zeroTail 0 ≠ 0 := by
  rw [zeroTail_eq, actualH_at_zero]
  simpa using (show (firstLiMass : ℂ) ≠ 0 by exact_mod_cast firstLiMass_pos.ne')

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact zeroTail_at_zero_ne ((zeroTail_eq 0).trans (h 0).symm)

private theorem zeroTail_tendsto_atTop : Tendsto zeroTail atTop (𝓝 (0 : ℂ)) := by
  let term (u : ℝ) (k : ℕ) := actualCoeff k * Complex.exp ((actualZero k - 1) * (u : ℂ))
  have hre (k : ℕ) : (actualZero k).re - 1 < 0 :=
    sub_neg.mpr (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2
  have hnorm (u : ℝ) (k : ℕ) :
      ‖term u k‖ = ‖actualCoeff k‖ * Real.exp (((actualZero k).re - 1) * u) := by
    simp [term, Complex.norm_exp, Complex.mul_re, Complex.sub_re]
  have hterm (k : ℕ) : Tendsto (fun u : ℝ => term u k) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have harg : Tendsto (fun u : ℝ => ((actualZero k).re - 1) * u) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (hre k)).mpr tendsto_id
    simpa only [hnorm, Function.comp_apply, mul_zero] using
      (Real.tendsto_exp_atBot.comp harg).const_mul ‖actualCoeff k‖
  have hbound : ∀ᶠ u : ℝ in atTop, ∀ k : ℕ, ‖term u k‖ ≤ ‖actualCoeff k‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu k
    rw [hnorm]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (hre k).le hu))
  change Tendsto (fun u : ℝ => ∑' k : ℕ, term u k) atTop (𝓝 (0 : ℂ))
  simpa only [tsum_zero] using
    tendsto_tsum_of_dominated_convergence actualCoeff_hasSum.summable.norm hterm hbound

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  by_contra h
  have heq (u : ℝ) : zeroTail u = zeroTail 0 := by
    by_contra hu
    exact h ⟨(), u, 0, hu⟩
  have hzero : Tendsto (fun _ : ℝ => zeroTail 0) atTop (𝓝 (0 : ℂ)) :=
    zeroTail_tendsto_atTop.congr' (Eventually.of_forall heq)
  exact zeroTail_at_zero_ne (tendsto_nhds_unique tendsto_const_nhds hzero)

def family : Registration arena (type_of% @zeroTail_eq) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@zeroTail_eq, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@zeroTail_eq) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.zeroTail_eq.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SquareSpectrum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => zeroTail u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SquareSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev densitySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

private def densityActual : Realization densitySignature :=
  realize densitySignature (fun _ _ u => squareDensity u) (fun e => nomatch e)

private def densityShifted : Realization densitySignature :=
  realize densitySignature (fun _ _ u => squareDensity u + 1) (fun e => nomatch e)

private def densityCoeff (k : ℕ) : ℂ := -2 / (actualZero k * (2 - actualZero k))

private lemma densityCoeff_norm_summable : Summable (fun k => ‖densityCoeff k‖) := by
  apply (actualCoeff_hasSum.summable.norm.mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  have hstrip : (actualZero k).re < 1 :=
    (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2
  have hg : ‖1 - actualZero k‖ ≤ ‖2 - actualZero k‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith
  have hd : 0 < ‖2 - actualZero k‖ := by
    apply lt_of_lt_of_le _ (Complex.abs_re_le_norm (2 - actualZero k))
    rw [Complex.sub_re, Complex.re_ofNat, abs_of_pos (by linarith)]
    linarith
  have hc : densityCoeff k = -2 * actualCoeff k * (1 - actualZero k) / (2 - actualZero k) := by
    have h₁ : 1 - actualZero k ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      simp [Complex.sub_re] at hh
      linarith
    unfold densityCoeff actualCoeff
    field_simp
  rw [hc, norm_div, norm_mul, norm_mul, norm_neg, Complex.norm_two]
  exact (div_le_iff₀ hd).2
    (mul_le_mul_of_nonneg_left hg (by positivity))

private lemma densityCoeff_re_neg (k : ℕ) : (densityCoeff k).re < 0 := by
  have h := (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2
  change 0 < (actualZero k).re ∧ (actualZero k).re < 1 at h
  let d := actualZero k * (2 - actualZero k)
  have hp : 0 < d.re := by
    dsimp [d]
    norm_num [Complex.mul_re, Complex.sub_re, Complex.sub_im]
    nlinarith [mul_pos h.1 (show 0 < 2 - (actualZero k).re by linarith),
      sq_nonneg (actualZero k).im]
  have hd : d ≠ 0 := by
    intro hz
    simp [hz] at hp
  change ((-2 : ℂ) / d).re < 0
  rw [Complex.div_re]
  norm_num
  exact div_neg_of_neg_of_pos (by linarith) (Complex.normSq_pos.mpr hd)

private theorem squareDensity_at_zero_neg : squareDensity 0 < 0 := by
  change (∑' k, densityCoeff k * Complex.exp ((actualZero k - 1) * ((0 : ℂ) / 2))).re < 0
  simp only [zero_div, mul_zero, Complex.exp_zero, mul_one]
  have h := (Complex.hasSum_re densityCoeff_norm_summable.of_norm.hasSum)
  rw [← h.tsum_eq, ← tsum_zero (L := SummationFilter.unconditional ℕ) (α := ℝ)]
  exact Summable.tsum_lt_tsum (fun k => (densityCoeff_re_neg k).le) (densityCoeff_re_neg 0)
    h.summable summable_zero

private theorem squareDensity_tendsto_atTop : Tendsto squareDensity atTop (𝓝 0) := by
  let term (u : ℝ) (k : ℕ) := densityCoeff k * Complex.exp ((actualZero k - 1) * ((u : ℂ) / 2))
  have hre (k : ℕ) : (actualZero k).re - 1 < 0 :=
    sub_neg.mpr (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2
  have hnorm (u : ℝ) (k : ℕ) :
      ‖term u k‖ = ‖densityCoeff k‖ * Real.exp (((actualZero k).re - 1) / 2 * u) := by
    dsimp only [term]
    rw [norm_mul, Complex.norm_exp]
    congr 2
    norm_num [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.sub_re]
    ring
  have hterm (k : ℕ) : Tendsto (fun u : ℝ => term u k) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have harg : Tendsto (fun u : ℝ => ((actualZero k).re - 1) / 2 * u) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (div_neg_of_neg_of_pos (hre k) (by norm_num))).mpr tendsto_id
    simpa only [hnorm, Function.comp_apply, mul_zero] using
      (Real.tendsto_exp_atBot.comp harg).const_mul ‖densityCoeff k‖
  have hbound : ∀ᶠ u : ℝ in atTop, ∀ k : ℕ, ‖term u k‖ ≤ ‖densityCoeff k‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu k
    rw [hnorm]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [hre k]) hu))
  have hs : Tendsto (fun u : ℝ => ∑' k, term u k) atTop (𝓝 (0 : ℂ)) := by
    simpa only [tsum_zero] using
      tendsto_tsum_of_dominated_convergence densityCoeff_norm_summable hterm hbound
  have hc : Tendsto Complex.re (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa only [Complex.zero_re] using Complex.continuous_re.continuousAt.tendsto (x := (0 : ℂ))
  exact hc.comp hs

private theorem density_dependence : ObservationalDependence densitySignature densityActual := by
  intro i
  by_contra h
  have heq (u : ℝ) : squareDensity u = squareDensity 0 := by
    by_contra hu
    exact h ⟨(), u, 0, hu⟩
  have hzero : Tendsto (fun _ : ℝ => squareDensity 0) atTop (𝓝 0) :=
    squareDensity_tendsto_atTop.congr' (Eventually.of_forall heq)
  exact squareDensity_at_zero_neg.ne (tendsto_nhds_unique tendsto_const_nhds hzero)

namespace Transform

abbrev arena : Arena where
  signature := densitySignature
  Law R := ∀ u : ℝ,
    let y := Real.exp (u / 2)
    2 * (-(zeroTail (Real.log y)).re +
      y * (∫ s in Ioi y, s ^ (-2 : ℝ) * (zeroTail (Real.log s)).re)) = R.readout () () u

theorem source_reconstruction : (type_of% @square_spectral_transform) ↔
    arena.Law densityActual := Iff.rfl

theorem rejected_law : ¬ arena.Law densityShifted := by
  intro h
  have hbad := h 0
  change _ = squareDensity 0 + 1 at hbad
  have hactual := square_spectral_transform 0
  dsimp only at hbad hactual
  linarith only [hbad, hactual]

def family : Registration arena (type_of% @square_spectral_transform) where
  actual := densityActual
  bridge := source_reconstruction
  variation := ⟨@square_spectral_transform, densityShifted, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law densityActual
    densityShifted rejected_law
  dependence := density_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@square_spectral_transform) (Realization densitySignature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.square_spectral_transform.__information_unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SquareSpectrum.Transform.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize densitySignature (fun _ _ u => squareDensity u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SquareSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Transform

namespace DensityIntegral

abbrev arena : Arena where
  signature := densitySignature
  Law R := ∀ a b : ℝ, IntervalIntegrable squareDensity volume a b ∧
    (∫ u in a..b, R.readout () () u) = squarePrimitive (Real.exp b) - squarePrimitive (Real.exp a)

theorem source_reconstruction : (type_of% @square_density_integral) ↔
    arena.Law densityActual := Iff.rfl

theorem rejected_law : ¬ arena.Law densityShifted := by
  intro h
  obtain ⟨hi, hactual⟩ := square_density_integral 0 1
  have hbad := (h 0 1).2
  change (∫ u in (0 : ℝ)..1, squareDensity u + 1) = _ at hbad
  rw [intervalIntegral.integral_add hi intervalIntegrable_const,
    intervalIntegral.integral_const] at hbad
  norm_num at hactual hbad
  linarith only [hbad, hactual]

def family : Registration arena (type_of% @square_density_integral) where
  actual := densityActual
  bridge := source_reconstruction
  variation := ⟨@square_density_integral, densityShifted, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law densityActual
    densityShifted rejected_law
  dependence := density_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@square_density_integral) (Realization densitySignature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.square_density_integral.__information_unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SquareSpectrum.DensityIntegral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize densitySignature (fun _ _ u => squareDensity u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SquareSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn", "fn", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DensityIntegral

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SquareSpectrum
