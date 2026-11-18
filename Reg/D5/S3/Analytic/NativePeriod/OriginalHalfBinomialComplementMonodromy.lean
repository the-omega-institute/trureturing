import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy
import Reg.Support.SingleDependentReadout

/-! Typed observation families for the complete native local-chart statements. -/

noncomputable section
open scoped Classical Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter

namespace Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod (period)
open _root_.D5.S3.Analytic.OriginalHalfBinomialDiskCorrection
open _root_.D5.S3.Analytic.OriginalHalfBinomialContinuation
open _root_.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy

open unitInterval
open _root_.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
open _root_.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy
open _root_.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy
namespace Equations
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ) (fun _ => ℂ) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ r v => decide (v = r)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ (z : ℂ),
    DifferentiableOn ℂ complementN (complementDomain z) ∧
    DifferentiableOn ℂ (complementY z) (complementDomain z) ∧
    (∀ r ∈ complementDomain z,
      DifferentiableAt ℂ (deriv complementN) r ∧
      DifferentiableAt ℂ (deriv (complementY z)) r ∧
      r * (1 - r) * deriv (deriv complementN) r +
        (1 - 2 * r) * deriv complementN r - (1 / 4 : ℂ) * complementN r = 0 ∧
      r * (1 - r) * deriv (deriv (complementY z)) r +
        (1 - 2 * r) * deriv (complementY z) r - (1 / 4 : ℂ) * complementY z r = 0 ∧
      M.readout () (-Complex.I / ((Real.pi : ℂ) * r * (1 - r)))
        (deriv complementN r * complementY z r - complementN r * deriv (complementY z) r) = true)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : (-1 : ℂ) ∈ E := by norm_num [E]
  have hd : 1 - Complex.exp (-1 : ℂ) ∈ complementDomain (-1) := by
    simpa [complementDomain] using (native_chart (-1) hz).2.1
  have hh := ((h (-1)).2.2 _ hd).2.2.2.2
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% @complementary_equations) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @complementary_equations,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complementary_equations) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy.Equations.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy.Equations.family
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
    owner := `D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg", "fn", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Equations

namespace Path
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (C(I, ℂ)) (fun _ => C(I, ℂ)) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ γ L => decide (NativeCharts (complementPath γ) L)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ (γ : C(I, ℂ))
    (hD : ∀ t, ‖1 - γ t‖ < 1) (hn : ∀ t, γ t ≠ 1) (hb : γ 0 = b),
    ∃ L : C(I, ℂ), L 0 = baseLog ∧ M.readout () γ L = true ∧
      (∀ t, ∀ᶠ s in 𝓝 t, complementY (L t) =ᶠ[𝓝 (γ s)] complementY (L s)) ∧
      complementY (L 0) =ᶠ[𝓝 b] period
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (ContinuousMap.const I b) (by intro t; norm_num [b])
    (by intro t; norm_num [b]) (by rfl)
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hg := positive_one_monodromy.1
  have hn : ¬ NativeCharts (complementPath gamma1) (ContinuousMap.const I (0 : ℂ)) := by
    intro h
    have he := h.projection 0
    norm_num [gamma1, complementPath, gamma0, b] at he
  refine ⟨gamma1, positiveLift, ContinuousMap.const I (0 : ℂ), ?_⟩
  simp [actual, realize, hg, hn]
def family : Registration arena (type_of% @complementary_path_continuation) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @complementary_path_continuation,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complementary_path_continuation) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy.Path.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy.Path.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ γ L => decide (NativeCharts (complementPath γ) L)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy
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
  realize signature (fun _ γ L => decide (NativeCharts (complementPath γ) L)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ (γ : C(I, ℂ))
    (hD : ∀ t, ‖1 - γ t‖ < 1) (hn : ∀ t, γ t ≠ 1)
    (hb : γ 0 = b) (hb1 : γ 1 = b),
    ∃ L : C(I, ℂ), ∃ k : ℤ, L 0 = baseLog ∧ M.readout () γ L = true ∧
      L 1 = baseLog + deck k ∧
      complementY (L 0) =ᶠ[𝓝 b] period ∧
      complementY (L 1) =ᶠ[𝓝 b]
        (fun r => period r - 2 * k * Complex.I * period (1 - r))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (ContinuousMap.const I b) (by intro t; norm_num [b])
    (by intro t; norm_num [b]) (by rfl) (by rfl)
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hg := positive_one_monodromy.1
  have hn : ¬ NativeCharts (complementPath gamma1) (ContinuousMap.const I (0 : ℂ)) := by
    intro h
    have he := h.projection 0
    norm_num [gamma1, complementPath, gamma0, b] at he
  refine ⟨gamma1, positiveLift, ContinuousMap.const I (0 : ℂ), ?_⟩
  simp [actual, realize, hg, hn]
def family : Registration arena (type_of% @complementary_loop_monodromy) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @complementary_loop_monodromy,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complementary_loop_monodromy) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy.Loop.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy.Loop.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ γ L => decide (NativeCharts (complementPath γ) L)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy
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
  realize signature (fun _ γ L => decide (NativeCharts (complementPath γ) L)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := M.readout () gamma1 positiveLift = true ∧
    complementY (positiveLift 0) =ᶠ[𝓝 b] period ∧
    complementY (positiveLift 1) =ᶠ[𝓝 b]
      (fun r => period r - 2 * Complex.I * period (1 - r))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  simpa [arena, rejected, realize] using h.1
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hg := positive_one_monodromy.1
  have hn : ¬ NativeCharts (complementPath gamma1) (ContinuousMap.const I (0 : ℂ)) := by
    intro h
    have he := h.projection 0
    norm_num [gamma1, complementPath, gamma0, b] at he
  refine ⟨gamma1, positiveLift, ContinuousMap.const I (0 : ℂ), ?_⟩
  simp [actual, realize, hg, hn]
def family : Registration arena (type_of% @positive_one_monodromy) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @positive_one_monodromy,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_one_monodromy) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy.Positive.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ γ L => decide (NativeCharts (complementPath γ) L)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg", "fn", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Positive

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
    ∀ᶠ s in 𝓝 r, M.readout () (period s) (complementY (Complex.log (1 - r)) s) = true
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb : b ∈ lens := by norm_num [b, lens, Metric.mem_ball, dist_eq_norm]
  obtain ⟨s, hs⟩ := (h b hb).exists
  simpa [rejected, realize] using hs
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% @complementary_initial_germ) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @complementary_initial_germ,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complementary_initial_germ) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy.Initial.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy.Initial.family
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
    owner := `D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg", "fn", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Initial

end Reg.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy
