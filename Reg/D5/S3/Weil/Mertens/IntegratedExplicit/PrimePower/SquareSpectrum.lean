import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SquareSpectrum
import Reg.Support.SingleDependentReadout

/-! Source audit of the actual zero-tail normalization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit
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

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SquareSpectrum
