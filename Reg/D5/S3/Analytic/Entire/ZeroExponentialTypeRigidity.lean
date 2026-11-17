import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Entire.ZeroExponentialTypeRigidity
import Reg.Support.DependentFamily

/-! Source-bound interventions on actual comparisons, equality or product convergence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

open Filter
open scoped BigOperators Topology
open _root_.D5.S3.Analytic.Entire
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Entire.ZeroExponentialTypeRigidity

namespace eq_at_zero_of_zero_exponential_type_of_bounded_real

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℂ,
      ‖f z‖ ≤ A * Real.exp (ε * ‖z‖))
    {B : ℝ} (hreal : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ B),
    ∀ z : ℂ, R.readout () () (f z) (f 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (differentiable_const (0 : ℂ)) (by intro ε hε; exact ⟨0, by simp⟩)
    (B := 0) (by simp) 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℂ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero hh

def source_registration : Registration arena (type_of% @_root_.D5.S3.Analytic.Entire.eq_at_zero_of_zero_exponential_type_of_bounded_real) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.Entire.eq_at_zero_of_zero_exponential_type_of_bounded_real, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.Entire.eq_at_zero_of_zero_exponential_type_of_bounded_real) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Entire.ZeroExponentialTypeRigidity.eq_at_zero_of_zero_exponential_type_of_bounded_real.unit
  realizationName := `Reg.D5.S3.Analytic.Entire.ZeroExponentialTypeRigidity.eq_at_zero_of_zero_exponential_type_of_bounded_real.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Entire.ZeroExponentialTypeRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end eq_at_zero_of_zero_exponential_type_of_bounded_real

namespace eq_zero_of_zero_exponential_type_of_reflection_of_tendsto_zero

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℂ → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℂ,
      ‖f z‖ ≤ A * Real.exp (ε * ‖z‖))
    (hreflection : ∀ z : ℂ, f (1 - z) = f z)
    (hlimit : Tendsto (fun x : ℝ => f (x : ℂ)) atTop (𝓝 0)),
    R.readout () () f 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (differentiable_const (0 : ℂ)) (by intro ε hε; exact ⟨0, by simp⟩)
    (by simp) tendsto_const_nhds

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ → ℂ), (1 : ℂ → ℂ), ?_⟩
  intro h
  have hh : (1 : ℂ → ℂ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero (congrFun hh 0)

def source_registration : Registration arena (type_of% @_root_.D5.S3.Analytic.Entire.eq_zero_of_zero_exponential_type_of_reflection_of_tendsto_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.Entire.eq_zero_of_zero_exponential_type_of_reflection_of_tendsto_zero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.Entire.eq_zero_of_zero_exponential_type_of_reflection_of_tendsto_zero) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Entire.ZeroExponentialTypeRigidity.eq_zero_of_zero_exponential_type_of_reflection_of_tendsto_zero.unit
  realizationName := `Reg.D5.S3.Analytic.Entire.ZeroExponentialTypeRigidity.eq_zero_of_zero_exponential_type_of_reflection_of_tendsto_zero.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Entire.ZeroExponentialTypeRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end eq_zero_of_zero_exponential_type_of_reflection_of_tendsto_zero

end Reg.D5.S3.Analytic.Entire.ZeroExponentialTypeRigidity
