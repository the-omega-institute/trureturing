import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.PositiveLaplaceContinuation
import Reg.Support.SingleDependentReadout

/-! Source selection of the terminal value of the continuation at a point of continuity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter LeanInformationAudit
open scoped Topology
open _root_.D5.S3.Analytic.Laplace.PositiveLaplaceContinuation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Analytic.Laplace.PositiveLaplaceContinuation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ → ℂ) (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ H z => H z) (fun e => nomatch e)

def shifted : Realization signature :=
  realize signature (fun _ H z => H z + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (_hXm : AEMeasurable X μ) (_hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    {a b : ℝ} (_hb : Integrable (fun ω => Real.exp (-b * X ω)) μ)
    {H : ℂ → ℂ} (_hHm : MeromorphicOn H {z | a < z.re})
    (_hHa : ∀ x : ℝ, a < x → x ≤ b → AnalyticAt ℂ H (x : ℂ))
    {z₀ : ℂ} (_ha₀ : a < z₀.re) (_hb₀ : b < z₀.re)
    (_hAgree : H =ᶠ[𝓝 z₀] fun z => complexMGF X μ (-z)),
    (∀ x : ℝ, a < x → Integrable (fun ω => Real.exp (-x * X ω)) μ) ∧
    AnalyticOnNhd ℂ (fun z => complexMGF X μ (-z)) {z | a < z.re} ∧
    ∀ z : ℂ, a < z.re →
      Integrable (fun ω => Complex.exp (-z * (X ω : ℂ))) μ ∧
      (H =ᶠ[𝓝[≠] z] fun w => complexMGF X μ (-w)) ∧
      (ContinuousAt H z → V.readout () H z = complexMGF X μ (-z))

private theorem shifted_fails : ¬ arena.{u}.Law shifted := by
  intro h
  have h0 := @h PUnit.{u + 1} inferInstance 0 (fun _ => 0)
    aemeasurable_const (ae_of_all _ fun _ => le_rfl) (-1) 0 integrable_zero_measure
    (fun _ => 0) (fun z _ => MeromorphicAt.const 0 z) (fun _ _ _ => analyticAt_const)
    1 (by norm_num) (by norm_num) (by simp [complexMGF])
  have he := (h0.2.2 0 (by norm_num)).2.2 continuous_const.continuousAt
  simpa [shifted, realize, complexMGF] using he

def family : Registration arena.{u}
    (type_of% @integrable_and_analytic_of_meromorphic_continuation.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integrable_and_analytic_of_meromorphic_continuation.{u}, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual shifted shifted_fails
  dependence := by
    intro i
    exact ⟨id, 0, 1, zero_ne_one⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrable_and_analytic_of_meromorphic_continuation.{u})
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.Laplace.PositiveLaplaceContinuation.integrable_and_analytic_of_meromorphic_continuation.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Laplace.PositiveLaplaceContinuation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ H z => H z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.PositiveLaplaceContinuation
    definition := none
    coordinates := #[9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 16
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

namespace AffineBound

open _root_.D5.S3.Analytic.Laplace.EulerPoleObstruction (kernel tailLaplace)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ → ℂ)
    (fun _ => Set ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ L S => AnalyticOnNhd ℂ L S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law Q := ∀ {f : ℝ → ℝ} {F : ℂ → ℂ} {a b U c A B : ℝ},
    0 ≤ U → a < b → Continuous f → c ≠ 0 →
    (∀ᶠ t in atTop, c * f t ≤ A * t + B) →
    (∀ s : ℂ, b < s.re → IntegrableOn (kernel f (s - a)) (Set.Ioi U)) →
    (∀ s : ℂ, b < s.re → F s = tailLaplace f U (s - a)) →
    MeromorphicOn F {s | a < s.re} →
    (∀ x : ℝ, a < x → AnalyticAt ℂ F (x : ℂ)) →
    ∃ L : ℂ → ℂ, Q.readout () () L {s | a < s.re} ∧
      ∀ s : ℂ, b < s.re → L s = F s

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, bad, _⟩ := h (f := fun _ => 0) (F := fun _ => 0)
    (a := 0) (b := 1) (U := 0) (c := 1) (A := 0) (B := 0)
    le_rfl zero_lt_one continuous_const one_ne_zero (by simp)
    (by intro s _; unfold kernel; simp) (by intro s _; simp [tailLaplace])
    (fun z _ => MeromorphicAt.const 0 z) (fun _ _ => analyticAt_const)
  exact bad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (fun _ : ℂ => (0 : ℂ)), (fun z : ℂ => z⁻¹), ?_⟩
  intro he
  have he' : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ =
      AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) Set.univ := congrFun he Set.univ
  have hi : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) Set.univ := by
    rw [← he']
    exact analyticOnNhd_const
  exact (differentiableAt_inv_iff.mp (hi 0 (Set.mem_univ 0)).differentiableAt) rfl

def family : Registration arena (type_of% @analytic_continuation_of_affine_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@analytic_continuation_of_affine_bound, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@analytic_continuation_of_affine_bound) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.Laplace.PositiveLaplaceContinuation.analytic_continuation_of_affine_bound.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Laplace.PositiveLaplaceContinuation.AffineBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ L S => AnalyticOnNhd ℂ L S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.PositiveLaplaceContinuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end AffineBound

end Reg.D5.S3.Analytic.Laplace.PositiveLaplaceContinuation
