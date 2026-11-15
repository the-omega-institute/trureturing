import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.PsiLaplaceContinuation
import Reg.Support.SingleDependentReadout
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData

noncomputable section
open Real Set MeasureTheory Filter Complex
open scoped Topology
open _root_.D5.S3.Weil.Mertens.PsiLaplaceContinuation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.PsiLaplaceContinuation

namespace SourceL1
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Set ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ F s => IntegrableOn F s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V := V.readout () () qpsi (Ioi (Real.log 2))
private theorem rejected_fails : ¬ arena.Law rejected := by
  exact fun h => h
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℝ)), (fun _ : ℝ => (1 : ℝ)), ?_⟩
  intro h
  have he := congrFun h (Ioi (1 : ℝ))
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi (1 : ℝ)) := by
    change IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi (1 : ℝ)) =
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi (1 : ℝ)) at he
    rw [← he]
    simp
  simpa [integrableOn_const_iff, Real.volume_Ioi] using hi
def family : Registration arena (type_of% @qpsi_integrable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@qpsi_integrable, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@qpsi_integrable) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.Mertens.PsiLaplaceContinuation.qpsi_integrable.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.PsiLaplaceContinuation.SourceL1.family
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
    owner := `D5.S3.Weil.Mertens.PsiLaplaceContinuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SourceL1

namespace FiniteCorrection
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ → ℂ)
    (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ F => Differentiable ℂ F) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V := ∀ U : ℝ, V.readout () () (Apsi U)
private theorem rejected_fails : ¬ arena.Law rejected := by
  exact fun h => h 0
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℂ => (0 : ℂ)), (fun z : ℂ => z⁻¹), ?_⟩
  intro he
  have hi : Differentiable ℂ (fun z : ℂ => z⁻¹) := by
    change Differentiable ℂ (fun _ : ℂ => (0 : ℂ)) =
      Differentiable ℂ (fun z : ℂ => z⁻¹) at he
    rw [← he]
    exact differentiable_const _
  exact (differentiableAt_inv_iff.mp (hi 0)) rfl
def family : Registration arena (type_of% @Apsi_entire) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Apsi_entire, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Apsi_entire) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.Mertens.PsiLaplaceContinuation.Apsi_entire.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.PsiLaplaceContinuation.FiniteCorrection.family
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
    owner := `D5.S3.Weil.Mertens.PsiLaplaceContinuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiniteCorrection

namespace Continuation
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V := ∀ (U : ℝ) {s : ℂ}, 0 < s.re → V.readout () () (Qpsi U s) (Mpsi U s)
private theorem rejected_fails : ¬ arena.Law rejected := by
  exact fun h => h 0 (s := 1) (by norm_num)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  intro h
  have he := congrFun h (0 : ℂ)
  change ((0 : ℂ) = 0) = ((1 : ℂ) = 0) at he
  have hh : (1 : ℂ) = 0 := he ▸ rfl
  exact one_ne_zero hh
def family : Registration arena (type_of% @Qpsi_eq_Mpsi) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Qpsi_eq_Mpsi, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Qpsi_eq_Mpsi) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.Mertens.PsiLaplaceContinuation.Qpsi_eq_Mpsi.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.PsiLaplaceContinuation.Continuation.family
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
    owner := `D5.S3.Weil.Mertens.PsiLaplaceContinuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Continuation

namespace RealCorridor
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ → ℂ)
    (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ F z => AnalyticAt ℂ F z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V := ∀ (U : ℝ) {x : ℝ}, (-1 : ℝ) < x → V.readout () () (Mpsi U) (x : ℂ)
private theorem rejected_fails : ¬ arena.Law rejected := by
  exact fun h => h 0 (x := 0) (by norm_num)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℂ => (0 : ℂ)), (fun z : ℂ => z⁻¹), ?_⟩
  intro h
  have he := congrFun h (0 : ℂ)
  have hi : AnalyticAt ℂ (fun z : ℂ => z⁻¹) 0 := by
    change AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) 0 =
      AnalyticAt ℂ (fun z : ℂ => z⁻¹) 0 at he
    rw [← he]
    exact analyticAt_const
  exact (differentiableAt_inv_iff.mp hi.differentiableAt) rfl
def family : Registration arena (type_of% @Mpsi_real_analytic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Mpsi_real_analytic, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Mpsi_real_analytic) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.Mertens.PsiLaplaceContinuation.Mpsi_real_analytic.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.PsiLaplaceContinuation.RealCorridor.family
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
    owner := `D5.S3.Weil.Mertens.PsiLaplaceContinuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RealCorridor

namespace SourcePoleOrder
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => WithTop ℤ)
    (fun _ => WithTop ℤ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V := ∀ (U : ℝ) {ρ : ℂ}, _root_.D5.S3.Weil.ZeroSum.IsNontrivialZero ρ →
    let a := ρ - 1
    let m := analyticOrderNatAt riemannZeta ρ
    let Λ := -(m : ℂ) / ρ
    a ∈ Dpsi ∧ a ≠ 0 ∧ a.im ≠ 0 ∧
    0 < m ∧ analyticOrderAt riemannZeta ρ ≠ ⊤ ∧ Λ ≠ 0 ∧
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧
      Mpsi U =ᶠ[𝓝[≠] a] (fun s => Λ / (s - a) + H s) ∧
      (fun s => -deriv (Mpsi U) s + Mpsi U s) =ᶠ[𝓝[≠] a]
        (fun s => Λ / (s - a) ^ 2 + Λ / (s - a) + H s - deriv H s) ∧
      V.readout () () (meromorphicOrderAt (Mpsi U) a) (-1 : ℤ) ∧
      meromorphicOrderAt (fun s => -deriv (Mpsi U) s + Mpsi U s) a = (-2 : ℤ)
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, _, _, _, _, H, _, _, _, hfalse, _⟩ := h 0 (_root_.D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData.zetaZeroData_isNontrivial 0)
  exact hfalse
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : WithTop ℤ), (1 : WithTop ℤ), ?_⟩
  intro h
  have he := congrFun h (0 : WithTop ℤ)
  change ((0 : WithTop ℤ) = 0) = ((1 : WithTop ℤ) = 0) at he
  have hh : (1 : WithTop ℤ) = 0 := he ▸ rfl
  exact one_ne_zero hh
def family : Registration arena (type_of% @actual_source_poles) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_source_poles, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_source_poles) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.Mertens.PsiLaplaceContinuation.actual_source_poles.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.PsiLaplaceContinuation.SourcePoleOrder.family
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
    owner := `D5.S3.Weil.Mertens.PsiLaplaceContinuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SourcePoleOrder

namespace SourceCoefficient
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => Filter ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ x => 𝓝 x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => 𝓝 (x + 1 : ℂ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V := ∀ (U : ℝ) {ρ : ℂ}, _root_.D5.S3.Weil.ZeroSum.IsNontrivialZero ρ →
    Tendsto (fun s : ℂ => (s - (ρ - 1)) * Mpsi U s) (𝓝[≠] (ρ - 1))
      (V.readout () () (-(analyticOrderNatAt riemannZeta ρ : ℂ) / ρ))
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hz := _root_.D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData.zetaZeroData_isNontrivial 0
  have he := tendsto_nhds_unique (source_normalized_limit 0 hz) (h 0 hz)
  have hb : (1 : ℂ) = 0 := by linear_combination -he
  exact one_ne_zero hb
def family : Registration arena (type_of% @source_normalized_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@source_normalized_limit, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    exact fun he => zero_ne_one (nhds_injective he)
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@source_normalized_limit) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.Mertens.PsiLaplaceContinuation.source_normalized_limit.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.PsiLaplaceContinuation.SourceCoefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨SourceCoefficient.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.PsiLaplaceContinuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SourceCoefficient

end Reg.D5.S3.Weil.Mertens.PsiLaplaceContinuation
