import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.ActualPsiTailEulerBridge
import Reg.Support.SingleDependentReadout

noncomputable section
open Real Set MeasureTheory Filter Complex
open scoped Topology
open _root_.D5.S3.Weil.Mertens.PsiLaplaceForcing
open _root_.D5.S3.Weil.Mertens.PsiLaplaceContinuation
open _root_.D5.S3.Analytic.Laplace.EulerPoleObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.ActualPsiTailEulerBridge

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
  unitName := `D5.S3.Weil.Mertens.ActualPsiTailEulerBridge.qpsi_integrable.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.ActualPsiTailEulerBridge.SourceL1.family
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
    owner := `D5.S3.Weil.Mertens.ActualPsiTailEulerBridge
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
  unitName := `D5.S3.Weil.Mertens.ActualPsiTailEulerBridge.Qpsi_eq_Mpsi.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.ActualPsiTailEulerBridge.Continuation.family
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
    owner := `D5.S3.Weil.Mertens.ActualPsiTailEulerBridge
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

namespace ActualTail
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V := ∀ u : ℝ, V.readout () () (fpsi u) (-(∫ v in Ioi u, kpsi v))
private theorem rejected_fails : ¬ arena.Law rejected := by
  exact fun h => h 0
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro h
  have he := congrFun h (0 : ℝ)
  change ((0 : ℝ) = 0) = ((1 : ℝ) = 0) at he
  have hh : (1 : ℝ) = 0 := he ▸ rfl
  exact one_ne_zero hh
def family : Registration arena (type_of% @fpsi_eq_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fpsi_eq_tail, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fpsi_eq_tail) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.Mertens.ActualPsiTailEulerBridge.fpsi_eq_tail.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.ActualPsiTailEulerBridge.ActualTail.family
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
    owner := `D5.S3.Weil.Mertens.ActualPsiTailEulerBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ActualTail

namespace ActualEuler
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Set ℝ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ F s => IntegrableOn F s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V := V.readout () () fpsi (Ioi (Real.log 2)) ∧
    ∀ U : ℝ, Real.log 2 ≤ U →
      AnalyticOnNhd ℂ (tailLaplace fpsi U) {z | 0 < z.re} ∧
      ∀ z : ℂ, 0 < z.re →
        (∀ n : ℕ, IntegrableOn (fun u : ℝ =>
          (u : ℂ) ^ n * Complex.exp (-z * (u : ℂ)) * (fpsi u : ℂ)) (Ioi U)) ∧
        HasDerivAt (tailLaplace fpsi U)
          (-(∫ u in Ioi U, (u : ℂ) * Complex.exp (-z * (u : ℂ)) * (fpsi u : ℂ))) z ∧
        HasDerivAt (deriv (tailLaplace fpsi U))
          (∫ u in Ioi U, (u : ℂ) ^ 2 * Complex.exp (-z * (u : ℂ)) * (fpsi u : ℂ)) z ∧
        euler (tailLaplace fpsi U) z = Phi U z
private theorem rejected_fails : ¬ arena.Law rejected := by
  exact fun h => h.1
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
def family : Registration arena (type_of% @actual_tail_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_tail_bridge, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_tail_bridge) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.Mertens.ActualPsiTailEulerBridge.actual_tail_bridge.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.ActualPsiTailEulerBridge.ActualEuler.family
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
    owner := `D5.S3.Weil.Mertens.ActualPsiTailEulerBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ActualEuler

end Reg.D5.S3.Weil.Mertens.ActualPsiTailEulerBridge
