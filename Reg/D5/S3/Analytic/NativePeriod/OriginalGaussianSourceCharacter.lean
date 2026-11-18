import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter
import Reg.Support.SingleDependentReadout

/-! Typed observation families for the complete native local-chart statements. -/

noncomputable section
open scoped Classical Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter

namespace Reg.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod (period)
open _root_.D5.S3.Analytic.OriginalHalfBinomialDiskCorrection
open _root_.D5.S3.Analytic.OriginalHalfBinomialContinuation
open _root_.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter

open unitInterval
open _root_.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialLocalCharts
open _root_.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialMonodromy
open _root_.D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy
open _root_.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators
namespace Branch
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ) (fun _ => ℂ) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ r v => decide (v = Complex.exp (-Complex.log (1 - r) / 2))) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := (∀ r ∈ disk, M.readout () r (C r) = true) ∧
    DifferentiableOn ℂ C disk ∧
    (∀ r ∈ disk, sourceMode false 0 r = C r)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.1 0 (by simp [disk])
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 1, 0, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% @actual_source_branch) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @actual_source_branch,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_source_branch) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter.Branch.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter.Branch.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r v => decide (v = Complex.exp (-Complex.log (1 - r) / 2))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Branch

namespace Deck
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℂ, ℤ) (fun _ => ℂ) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ p v => decide (v = (-1 : ℂ) ^ p.2 * sourceCover p.1)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := Differentiable ℂ sourceCover ∧
    (∀ z : ℂ, ∀ k : ℤ,
      M.readout () ⟨z, k⟩ (sourceCover (z + k * (2 * (Real.pi : ℂ) * Complex.I))) = true)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.2 0 0
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0⟩, 1, 0, ?_⟩
  norm_num [actual, realize, sourceCover]
def family : Registration arena (type_of% @source_deck) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @source_deck,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@source_deck) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter.Deck.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter.Deck.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => decide (v = (-1 : ℂ) ^ p.2 * sourceCover p.1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["arg", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Deck

namespace Path
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (C(I, ℂ)) (fun _ => C(I, ℂ)) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ γ L => decide (SourceCharts γ L)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ (γ : C(I, ℂ))
    (hD : ∀ t, ‖1 - γ t‖ < 1) (hn : ∀ t, γ t ≠ 1) (hb : γ 0 = b),
    ∃ L : C(I, ℂ), L 0 = baseLog ∧ NativeCharts (complementPath γ) L ∧ M.readout () γ L = true
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (ContinuousMap.const I b) (by intro t; norm_num [b])
    (by intro t; norm_num [b]) (by rfl)
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hg := positive_source_monodromy.1
  have hn : ¬ SourceCharts gamma1 ((0 : C(I, ℂ))) := by
    intro h
    have hy : gamma1 0 = b := by norm_num [gamma1, complementPath, gamma0, b]
    have hv : C b = 1 := h.initial.self_of_nhds.symm.trans (by
      simpa [hy, sourceCover] using h.liftValue 0)
    have hd : b ∈ disk := by norm_num [b, disk]
    have hs := (sourceMode_square (u := 0) (x := b) (by norm_num [b])).2
    rw [actual_source_branch.2.2 b hd, hv] at hs
    norm_num [b] at hs
  refine ⟨gamma1, positiveLift, (0 : C(I, ℂ)), ?_⟩
  simp [actual, realize, hg, hn]
def family : Registration arena (type_of% @actual_source_path) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @actual_source_path,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_source_path) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter.Path.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter.Path.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ γ L => decide (SourceCharts γ L)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Path

namespace Loop
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (C(I, ℂ)) (fun _ => C(I, ℂ)) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ γ L => decide (SourceCharts γ L)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := DifferentiableOn ℂ C disk ∧
    (∀ γ : C(I, ℂ), (∀ t, ‖γ t‖ < 1) →
      (∀ t, disk ∈ 𝓝 (γ t)) ∧
      (∀ t, ∀ᶠ s in 𝓝 t, C =ᶠ[𝓝 (γ s)] C) ∧
      C =ᶠ[𝓝 (γ 0)] C ∧ C =ᶠ[𝓝 (γ 1)] C) ∧
    (∀ γ : C(I, ℂ), (∀ t, ‖1 - γ t‖ < 1) → (∀ t, γ t ≠ 1) →
      γ 0 = b → γ 1 = b →
      ∃ L : C(I, ℂ), ∃ k : ℤ, L 0 = baseLog ∧ NativeCharts (complementPath γ) L ∧
        M.readout () γ L = true ∧ L 1 = baseLog + deck k ∧
        sourceChart (L 1) =ᶠ[𝓝 b] (fun r => (-1 : ℂ) ^ k * C r))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.2.2 (ContinuousMap.const I b) (by intro t; norm_num [b])
    (by intro t; norm_num [b]) (by rfl) (by rfl)
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hg := positive_source_monodromy.1
  have hn : ¬ SourceCharts gamma1 ((0 : C(I, ℂ))) := by
    intro h
    have hy : gamma1 0 = b := by norm_num [gamma1, complementPath, gamma0, b]
    have hv : C b = 1 := h.initial.self_of_nhds.symm.trans (by
      simpa [hy, sourceCover] using h.liftValue 0)
    have hd : b ∈ disk := by norm_num [b, disk]
    have hs := (sourceMode_square (u := 0) (x := b) (by norm_num [b])).2
    rw [actual_source_branch.2.2 b hd, hv] at hs
    norm_num [b] at hs
  refine ⟨gamma1, positiveLift, (0 : C(I, ℂ)), ?_⟩
  simp [actual, realize, hg, hn]
def family : Registration arena (type_of% @actual_source_loop_character) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @actual_source_loop_character,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_source_loop_character) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter.Loop.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter.Loop.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ γ L => decide (SourceCharts γ L)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "arg", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Loop

namespace Positive
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Unit) (fun _ => C(I, ℂ)) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ _ L => decide (SourceCharts gamma1 L)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := M.readout () () positiveLift = true ∧
    sourceChart (positiveLift 1) =ᶠ[𝓝 b] (fun r => -C r)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  simpa [arena, rejected, realize] using h.1
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hg := positive_source_monodromy.1
  have hn : ¬ SourceCharts gamma1 ((0 : C(I, ℂ))) := by
    intro h
    have hy : gamma1 0 = b := by norm_num [gamma1, complementPath, gamma0, b]
    have hv : C b = 1 := h.initial.self_of_nhds.symm.trans (by
      simpa [hy, sourceCover] using h.liftValue 0)
    have hd : b ∈ disk := by norm_num [b, disk]
    have hs := (sourceMode_square (u := 0) (x := b) (by norm_num [b])).2
    rw [actual_source_branch.2.2 b hd, hv] at hs
    norm_num [b] at hs
  refine ⟨(), positiveLift, (0 : C(I, ℂ)), ?_⟩
  simp [actual, realize, hg, hn]
def family : Registration arena (type_of% @positive_source_monodromy) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @positive_source_monodromy,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_source_monodromy) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter.Positive.unit
  realizationName := `Reg.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ L => decide (SourceCharts gamma1 L)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Positive

end Reg.D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter
