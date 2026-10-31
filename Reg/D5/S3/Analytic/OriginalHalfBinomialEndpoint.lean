import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.OriginalHalfBinomialEndpoint
import Reg.Support.SingleDependentReadout

/-! Original real period observations in the endpoint and nome limits. -/

noncomputable section
open _root_.D5.S3.Analytic
open _root_.D5.S3.Analytic.OriginalHalfBinomialEndpoint
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter
open scoped Topology

namespace Reg.D5.S3.Analytic.OriginalHalfBinomialEndpoint

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ r => (OriginalHalfBinomialPeriod.period (r : ℂ)).re)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem period_zero : OriginalHalfBinomialPeriod.period 0 = 1 := by
  have h := (OriginalHalfBinomialIntegral.original_series_eq_integral 0
    (by norm_num) (by norm_num)).2.2
  simpa [OriginalHalfBinomialPeriod.period, Real.pi_ne_zero] using h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  by_contra h
  push_neg at h
  have he : (fun r : ℝ => (OriginalHalfBinomialPeriod.period (r : ℂ)).re) =
      fun _ => (1 : ℝ) := by
    funext r
    have hh := h () r 0
    simpa [actual, realize, period_zero] using hh
  have hd := (OriginalHalfBinomialPeriod.picard_fuchs (z := 0)
    (by norm_num)).1.hasDerivAt.real_of_complex
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  have hp := congrArg Complex.re (OriginalHalfBinomialPeriod.picard_fuchs
    (z := 0) (by norm_num)).2.2
  norm_num [period_zero, hz] at hp

namespace Endpoint

def arena : Arena where
  signature := signature
  Law R := Tendsto (fun r : ℝ => Real.pi * R.readout () () (1 - r) + Real.log r)
    (𝓝[>] 0) (𝓝 (Real.log 16))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh : Tendsto Real.log (𝓝[>] 0) (𝓝 (Real.log 16)) := by
    simpa [arena, rejected, realize] using h
  exact not_tendsto_nhds_of_tendsto_atBot Real.tendsto_log_nhdsGT_zero _ hh

def family : Registration arena (type_of% @original_period_log16) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_period_log16, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_period_log16) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialEndpoint.Endpoint.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialEndpoint.Endpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ r => (OriginalHalfBinomialPeriod.period (r : ℂ)).re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialEndpoint
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Endpoint

namespace Nome

def arena : Arena where
  signature := signature
  Law R := Tendsto (fun r : ℝ =>
    Real.exp (-Real.pi * (OriginalHalfBinomialPeriod.period ((1 - r : ℝ) : ℂ)).re /
      R.readout () () r) / r)
    (𝓝[>] 0) (𝓝 (1 / 16))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh : Tendsto (fun r : ℝ => r⁻¹) (𝓝[>] 0) (𝓝 (1 / 16)) := by
    simpa [arena, rejected, realize] using h
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_inv_nhdsGT_zero _ hh

def family : Registration arena (type_of% @original_nome_quotient) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_nome_quotient, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_nome_quotient) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialEndpoint.Nome.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialEndpoint.Nome.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ r => (OriginalHalfBinomialPeriod.period (r : ℂ)).re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialEndpoint
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Nome
end Reg.D5.S3.Analytic.OriginalHalfBinomialEndpoint
