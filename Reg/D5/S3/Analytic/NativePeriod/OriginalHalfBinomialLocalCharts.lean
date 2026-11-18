import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
import Reg.Support.SingleDependentReadout

/-! Typed observation families for the complete native local-chart statements. -/

noncomputable section
open scoped Classical Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter

namespace Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod (period)
open _root_.D5.S3.Analytic.OriginalHalfBinomialDiskCorrection
open _root_.D5.S3.Analytic.OriginalHalfBinomialContinuation
open _root_.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts

namespace Chart
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ) (fun _ => ℂ) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ r v => decide (Complex.exp v = r)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ z : ℂ, z ∈ E →
    IsOpen (chartDomain z) ∧ Complex.exp z ∈ chartDomain z ∧
    localLog z (Complex.exp z) = z ∧
    (∀ r ∈ chartDomain z, M.readout () r (localLog z r) = true ∧
      localLog z r ∈ E ∧ HasDerivAt (localLog z) (1 / r) r ∧
      chartT z r = T (localLog z r) ∧ chartN z r = N (localLog z r)) ∧
    (fun w => localLog z (Complex.exp w)) =ᶠ[𝓝 z] (fun w => w)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : (-1 : ℂ) ∈ E := by norm_num [E]
  have hh := ((h (-1) hz).2.2.2.1 _ (native_chart (-1) hz).2.1).1
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, Complex.log 2, ?_⟩
  norm_num [actual, realize, Complex.exp_log]
def family : Registration arena (type_of% @native_chart) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @native_chart,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_chart) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts.Chart.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts.Chart.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r v => decide (Complex.exp v = r)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "arg", "fn", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Chart

namespace Cover
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ) (fun _ => ℂ) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ r v => decide (v = r)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := DifferentiableOn ℂ T E ∧ DifferentiableOn ℂ Y E ∧ DifferentiableOn ℂ N E ∧
    (∀ z : ℂ, ∀ k : ℤ,
      T (z + k * (2 * (Real.pi : ℂ) * Complex.I)) = T z + 2 * k ∧
      M.readout () (Y z) (Y (z + k * (2 * (Real.pi : ℂ) * Complex.I))) = true ∧
      N (z + k * (2 * (Real.pi : ℂ) * Complex.I)) = N z + 2 * k * Y z)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h.2.2.2 0 0).2.1
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% @cover_periods) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @cover_periods,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cover_periods) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts.Cover.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts.Cover.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r v => decide (v = r)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["arg", "arg", "arg", "body", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Cover

namespace Equations
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ) (fun _ => ℂ → ℂ) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ r f => decide (HasDerivAt f (-Complex.I / ((Real.pi : ℂ) * r * (1 - r) * period r ^ 2)) r)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ z : ℂ,
    DifferentiableOn ℂ (chartT z) (chartDomain z) ∧
    DifferentiableOn ℂ (chartN z) (chartDomain z) ∧
    (∀ r ∈ chartDomain z,
      M.readout () r (chartT z) = true ∧
      DifferentiableAt ℂ (deriv (chartN z)) r ∧
      r * (1 - r) * deriv (deriv (chartN z)) r +
        (1 - 2 * r) * deriv (chartN z) r - (1 / 4 : ℂ) * chartN z r = 0 ∧
      deriv (chartN z) r * period r - chartN z r * deriv period r =
        -Complex.I / ((Real.pi : ℂ) * r * (1 - r)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : (-1 : ℂ) ∈ E := by norm_num [E]
  have hh := ((h (-1)).2.2 _ (native_chart (-1) hz).2.1).1
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ : ℂ => (0 : ℂ)), (fun z : ℂ => z), ?_⟩
  have hn : ¬ HasDerivAt (fun z : ℂ => z) (0 : ℂ) 0 := by
    intro h
    have he := h.unique (hasDerivAt_id (0 : ℂ))
    norm_num at he
  simp [actual, realize, hn, hasDerivAt_const]
def family : Registration arena (type_of% @chart_equations) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @chart_equations,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chart_equations) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts.Equations.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts.Equations.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r f => decide (HasDerivAt f (-Complex.I / ((Real.pi : ℂ) * r * (1 - r) * period r ^ 2)) r)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "arg", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Equations

namespace Transition
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ) (fun _ => ℂ) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ r v => decide (v = r)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ z w : ℂ, w ∈ E → (w - z).im ∈ Ioo (-Real.pi) Real.pi →
    (∀ᶠ r in 𝓝 (Complex.exp w), M.readout () (localLog w r) (localLog z r) = true) ∧
    chartT z =ᶠ[𝓝 (Complex.exp w)] chartT w ∧
    chartN z =ᶠ[𝓝 (Complex.exp w)] chartN w
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : (-1 : ℂ) ∈ E := by norm_num [E]
  have hzz : ((-1 : ℂ) - -1).im ∈ Ioo (-Real.pi) Real.pi := by simp [Real.pi_pos]
  obtain ⟨r, hr⟩ := (h (-1) (-1) hz hzz).1.exists
  simpa [rejected, realize] using hr
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% @chart_transition) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @chart_transition,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chart_transition) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts.Transition.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts.Transition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r v => decide (v = r)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
    definition := none
    coordinates := #[0,1]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Transition

namespace Initial
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ) (fun _ => ℂ) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ r v => decide (v = r)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ r : ℂ, r ∈ lens →
    Complex.log r ∈ E ∧
    (∀ᶠ s in 𝓝 r, M.readout () (Complex.I * period (1 - s)) (chartN (Complex.log r) s) = true) ∧
    chartT (Complex.log r) =ᶠ[𝓝 r] OriginalHalfBinomialWronskian.tau
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb : (1 / 2 : ℂ) ∈ lens := by norm_num [lens, Metric.mem_ball, dist_eq_norm]
  obtain ⟨r, hr⟩ := (h (1 / 2) hb).2.1.exists
  simpa [rejected, realize] using hr
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% @native_initial_germ) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @native_initial_germ,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_initial_germ) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts.Initial.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts.Initial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r v => decide (v = r)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Initial

end Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
