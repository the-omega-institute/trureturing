import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.CanonicalProducts.SummableLinearProduct
import Reg.Support.DependentFamily

/-! Source-bound interventions on actual comparisons, equality or product convergence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

open Filter
open scoped BigOperators Topology
open _root_.D5.S3.Analytic.CanonicalProducts.SummableLinearProduct
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.CanonicalProducts.SummableLinearProduct

namespace entire_zero_type_of_summable_norm

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} (c : I → ℂ)
    (hc : Summable (fun i => ‖c i‖)),
    (∀ z : ℂ, Multipliable (fun i => 1 + z * c i)) ∧
      Differentiable ℂ (fun z : ℂ => ∏' i, (1 + z * c i)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, R.readout () () 1 A ∧
        ∀ z : ℂ, ‖∏' i, (1 + z * c i)‖ ≤ A * Real.exp (ε * ‖z‖)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨A, hA, _⟩ := (@h (ULift.{u} Empty) (fun _ => 0) (by simp)).2.2 1 zero_lt_one
  exact hA

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  exact (not_le_of_gt zero_lt_one) hh

def source_registration : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.CanonicalProducts.SummableLinearProduct.entire_zero_type_of_summable_norm.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.CanonicalProducts.SummableLinearProduct.entire_zero_type_of_summable_norm.{u}, rejected, rejected_law⟩
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
      (@_root_.D5.S3.Analytic.CanonicalProducts.SummableLinearProduct.entire_zero_type_of_summable_norm.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CanonicalProducts.SummableLinearProduct.entire_zero_type_of_summable_norm.unit
  realizationName := `Reg.D5.S3.Analytic.CanonicalProducts.SummableLinearProduct.entire_zero_type_of_summable_norm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CanonicalProducts.SummableLinearProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "body", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end entire_zero_type_of_summable_norm

end Reg.D5.S3.Analytic.CanonicalProducts.SummableLinearProduct
