import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint
import Reg.Support.SingleDependentReadout

/-! The endpoint weight is the observed output in both bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Real Set LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualSignedGaussianEndpoint
  (actualCompleteSpectrum)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ b => W b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  norm_num [actual, realize, W]

namespace Mode

def arena : Arena where
  signature := signature
  Law R := ∀ {z : ℂ}, z.re ≤ 1 → (1 : ℂ) - z ≠ 0 → ∀ {b : ℝ}, 0 < b →
    ‖resolventMode z b‖ ≤ R.readout () () b * exp ((z.re - 1) * b) / ‖(1 : ℂ) - z‖

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (z := 0) (by norm_num) (by norm_num) (b := 1) (by norm_num)
  norm_num [rejected, realize] at hh
  linarith [norm_nonneg (resolventMode 0 1), exp_pos (-1 : ℝ)]

def evidence : Registration arena (type_of% @resolventMode_norm_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@resolventMode_norm_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@resolventMode_norm_le) (Realization signature) Unit Unit where
  unitName :=
    .str `D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint.resolventMode_norm_le
      "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint.Mode.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => W b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Mode

namespace Tail

def arena : Arena where
  signature := signature
  Law R := ∀ {b T : ℝ}, 0 < b → 0 < T →
    (∀ k ∈ lowHeight T, (actualZero k).re = 1 / 2) →
    (lowHeight T).Finite ∧
    ‖spectralTail actualCompleteSpectrum b‖ ≤
      R.readout () () b * (exp (-b / 2) * cubicLowMass T + quadraticHighMass T / T) ∧
    quadraticHighMass T ≤ (101 / 100 : ℝ) * firstLiMass

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hnone (k : ℕ) (hk : k ∈ lowHeight 1) : False := by
    have hle : |(actualZero k).im| ≤ 1 := hk
    have hgt : 10 < |(actualZero k).im| := actualCompleteSpectrum.height k
    linarith only [hgt, hle]
  have hbad := (h (b := 1) (T := 1) one_pos one_pos fun k hk => (hnone k hk).elim).2.1
  have hsum : Summable (fun k : ℕ => 1 / |(actualZero k).im| ^ 2) := by
    simpa only [Function.comp_def, actualZero, sq_abs, one_div, inv_pow] using
      (actualOccurrenceEquiv.summable_iff).2 actual_sigma_inverse_square_summable
  have hq : 0 < quadraticHighMass 1 := by
    let k : ((lowHeight 1)ᶜ : Set ℕ) := ⟨0, hnone 0⟩
    have hp : 0 < |(actualZero (k : ℕ)).im| :=
      (by norm_num : (0 : ℝ) < 10).trans (actualCompleteSpectrum.height k)
    exact (hsum.subtype ((lowHeight 1)ᶜ : Set ℕ)).tsum_pos
      (fun i => show 0 ≤ 1 / |(actualZero i.val).im| ^ 2 by positivity) k
      (show 0 < 1 / |(actualZero (k : ℕ)).im| ^ 2 by positivity)
  have hc : 0 ≤ cubicLowMass 1 := tsum_nonneg (fun _ => by positivity)
  change ‖spectralTail actualCompleteSpectrum 1‖ ≤
    -1 * (exp (-(1 : ℝ) / 2) * cubicLowMass 1 + quadraticHighMass 1 / 1) at hbad
  have hterm := mul_nonneg (exp_nonneg (-(1 : ℝ) / 2)) hc
  linarith [norm_nonneg (spectralTail actualCompleteSpectrum 1)]

def evidence : Registration arena (type_of% @actual_spectral_tail_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_spectral_tail_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_spectral_tail_bound) (Realization signature) Unit Unit where
  unitName :=
    .str `D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint.actual_spectral_tail_bound
      "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint.Tail.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => W b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Tail

#print axioms Mode.audit
#print axioms Tail.audit

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint
