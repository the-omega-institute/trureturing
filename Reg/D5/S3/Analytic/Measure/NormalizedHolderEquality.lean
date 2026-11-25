import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Measure.NormalizedHolderEquality
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.Measure.NormalizedHolderEquality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory
open scoped ENNReal BigOperators

namespace Reg.D5.S3.Analytic.Measure.NormalizedHolderEquality
noncomputable section
universe u v

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ≥0∞) (fun _ => ℝ≥0∞ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ a b => a = b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} {J : Type v} [MeasurableSpace X] [Fintype J]
    (μ : Measure X) (q : J → X → ℝ≥0∞) (w : J → ℝ)
    (_hq : ∀ j, AEMeasurable (q j) μ) (_hi : ∀ j, ∫⁻ x, q j x ∂μ = 1)
    (_hw : ∀ j, 0 < w j) (_hs : ∑ j, w j = 1),
    R.readout () () (∫⁻ x, ∏ j, q j x ^ w j ∂μ) 1 ↔ ∀ j k, q j =ᵐ[μ] q k

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  letI : MeasurableSpace (ULift.{u} Unit) := ⊤
  have H := @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance
    (Measure.dirac (ULift.up ())) (fun _ _ => 1) (fun _ => 1)
    (fun _ => aemeasurable_const) (by intro j; simp)
    (by intro j; norm_num) (by simp)
  exact H.mpr (fun _ _ => Filter.EventuallyEq.rfl)

def family : Registration arena.{u,v} (type_of% @lintegral_prod_rpow_eq_one_iff.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lintegral_prod_rpow_eq_one_iff.{u,v}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have H := congrFun h 0
    have hz : (0 : ℝ≥0∞) = 0 := rfl
    exact ENNReal.zero_ne_one (H.mp hz).symm

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lintegral_prod_rpow_eq_one_iff.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Measure.NormalizedHolderEquality.lintegral_prod_rpow_eq_one_iff.audit
  realizationName := `Reg.D5.S3.Analytic.Measure.NormalizedHolderEquality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ (a b : ℝ≥0∞) => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Measure.NormalizedHolderEquality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Measure.NormalizedHolderEquality
