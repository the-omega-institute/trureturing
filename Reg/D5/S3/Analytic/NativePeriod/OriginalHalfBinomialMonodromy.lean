import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy
import Reg.Support.SingleDependentReadout

/-! Typed observation families for the complete native local-chart statements. -/

noncomputable section
open scoped Classical Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter

namespace Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod (period)
open _root_.D5.S3.Analytic.OriginalHalfBinomialDiskCorrection
open _root_.D5.S3.Analytic.OriginalHalfBinomialContinuation
open _root_.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy

open unitInterval
open _root_.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
open _root_.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy
namespace Path
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (C(I, ℂ)) (fun _ => C(I, ℂ)) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ γ L => decide (NativeCharts γ L)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ (γ : C(I, ℂ)) (hD : ∀ t, ‖γ t‖ < 1)
    (hn : ∀ t, γ t ≠ 0) (hb : γ 0 = b),
    ∃! L : C(I, ℂ), L 0 = baseLog ∧ M.readout () γ L = true
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (ContinuousMap.const I b) (by intro t; norm_num [b])
    (by intro t; norm_num [b]) (by rfl)
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hg := positive_zero_monodromy.1
  have hn : ¬ NativeCharts gamma0 (ContinuousMap.const I (0 : ℂ)) := by
    intro h
    have he := h.projection 0
    norm_num [gamma0, b] at he
  refine ⟨gamma0, positiveLift, ContinuousMap.const I (0 : ℂ), ?_⟩
  simp [actual, realize, hg, hn]
def family : Registration arena (type_of% @native_path_continuation) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @native_path_continuation,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_path_continuation) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy.Path.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy.Path.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ γ L => decide (NativeCharts γ L)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg", "fn", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Path

namespace Loop
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (C(I, ℂ)) (fun _ => C(I, ℂ)) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ γ L => decide (NativeCharts γ L)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ (γ : C(I, ℂ)) (hD : ∀ t, ‖γ t‖ < 1)
    (hn : ∀ t, γ t ≠ 0) (hb : γ 0 = b) (hb1 : γ 1 = b),
    ∃ L : C(I, ℂ), ∃ k : ℤ, L 0 = baseLog ∧ M.readout () γ L = true ∧
      L 1 = baseLog + deck k ∧
      chartN (L 1) =ᶠ[𝓝 b]
        (fun r => Complex.I * period (1 - r) + 2 * k * period r) ∧
      chartT (L 1) =ᶠ[𝓝 b]
        (fun r => OriginalHalfBinomialWronskian.tau r + 2 * k)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (ContinuousMap.const I b) (by intro t; norm_num [b])
    (by intro t; norm_num [b]) (by rfl) (by rfl)
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hg := positive_zero_monodromy.1
  have hn : ¬ NativeCharts gamma0 (ContinuousMap.const I (0 : ℂ)) := by
    intro h
    have he := h.projection 0
    norm_num [gamma0, b] at he
  refine ⟨gamma0, positiveLift, ContinuousMap.const I (0 : ℂ), ?_⟩
  simp [actual, realize, hg, hn]
def family : Registration arena (type_of% @native_loop_monodromy) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @native_loop_monodromy,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_loop_monodromy) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy.Loop.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy.Loop.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ γ L => decide (NativeCharts γ L)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg", "fn", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Loop

namespace Positive
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (C(I, ℂ)) (fun _ => C(I, ℂ)) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ γ L => decide (NativeCharts γ L)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := M.readout () gamma0 positiveLift = true ∧ positiveLift 1 = baseLog + deck 1 ∧
    chartN (positiveLift 1) =ᶠ[𝓝 b]
      (fun r => Complex.I * period (1 - r) + 2 * period r)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  simpa [arena, rejected, realize] using h.1
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hg := positive_zero_monodromy.1
  have hn : ¬ NativeCharts gamma0 (ContinuousMap.const I (0 : ℂ)) := by
    intro h
    have he := h.projection 0
    norm_num [gamma0, b] at he
  refine ⟨gamma0, positiveLift, ContinuousMap.const I (0 : ℂ), ?_⟩
  simp [actual, realize, hg, hn]
def family : Registration arena (type_of% @positive_zero_monodromy) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @positive_zero_monodromy,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_zero_monodromy) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy.Positive.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ γ L => decide (NativeCharts γ L)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg", "fn", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Positive

end Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy
