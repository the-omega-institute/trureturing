import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.PsiLaplaceForcing
import Reg.Support.SingleDependentReadout
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData

noncomputable section
open Real Set MeasureTheory Filter Complex
open scoped Topology
open _root_.D5.S3.Weil.Mertens.PsiLaplaceContinuation
open _root_.D5.S3.Weil.Mertens.PsiLaplaceForcing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.PsiLaplaceForcing

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
  unitName := `D5.S3.Weil.Mertens.PsiLaplaceForcing.fpsi_eq_tail.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.PsiLaplaceForcing.ActualTail.family
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
    owner := `D5.S3.Weil.Mertens.PsiLaplaceForcing
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

namespace Boundary
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ → ℂ)
    (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ F z => AnalyticAt ℂ F z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V := ∀ (U : ℝ) (s : ℂ), V.readout () () (boundary U) s
private theorem rejected_fails : ¬ arena.Law rejected := by
  exact fun h => h 0 0
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
def family : Registration arena (type_of% @boundary_analytic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundary_analytic, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@boundary_analytic) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.Mertens.PsiLaplaceForcing.boundary_analytic.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.PsiLaplaceForcing.Boundary.family
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
    owner := `D5.S3.Weil.Mertens.PsiLaplaceForcing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Boundary

namespace ForcingPoleOrder
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
    a ∈ Dpsi ∧ a ≠ 0 ∧ a.im ≠ 0 ∧ 0 < m ∧ Λ ≠ 0 ∧
    meromorphicOrderAt (Mpsi U) a = (-1 : ℤ) ∧
    V.readout () () (meromorphicOrderAt (Phi U) a) (-2 : ℤ) ∧
    Tendsto (fun s : ℂ => (s - a) * Mpsi U s) (𝓝[≠] a) (𝓝 Λ) ∧
    Tendsto (fun s : ℂ => (s - a) ^ 2 * Phi U s) (𝓝[≠] a) (𝓝 Λ) ∧
    ∃ J : ℂ → ℂ, AnalyticAt ℂ J a ∧
      Phi U =ᶠ[𝓝[≠] a] (fun s => Λ / (s - a) ^ 2 + Λ / (s - a) + J s)
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, _, _, _, _, hfalse, _⟩ := h 0 (_root_.D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData.zetaZeroData_isNontrivial 0)
  exact hfalse
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : WithTop ℤ), (1 : WithTop ℤ), ?_⟩
  intro h
  have he := congrFun h (0 : WithTop ℤ)
  change ((0 : WithTop ℤ) = 0) = ((1 : WithTop ℤ) = 0) at he
  have hh : (1 : WithTop ℤ) = 0 := he ▸ rfl
  exact one_ne_zero hh
def family : Registration arena (type_of% @actual_forcing_poles) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_forcing_poles, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_forcing_poles) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.Mertens.PsiLaplaceForcing.actual_forcing_poles.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.PsiLaplaceForcing.ForcingPoleOrder.family
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
    owner := `D5.S3.Weil.Mertens.PsiLaplaceForcing
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
end ForcingPoleOrder

end Reg.D5.S3.Weil.Mertens.PsiLaplaceForcing
