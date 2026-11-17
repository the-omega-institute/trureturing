import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment
import Reg.Support.DependentFamily

/-! Full-source family with the endpoint identity's real equality as its observer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open _root_.D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment
namespace integrated_transverse_moment

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
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} (w a gamma : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1 / 2)
    (hgamma : ∀ i, 0 < gamma i)
    (hbudget : Summable (fun i => w i * (a i)^2 / (gamma i)^2)),
    (∀ i t, |w i * logKernel (a i) (gamma i) t| ≤
      2 * (w i * (a i)^2 / (gamma i)^2)) ∧
    HasSumUniformlyOn (fun i t => w i * logKernel (a i) (gamma i) t)
      (defect w a gamma) Set.univ ∧
    (∀ t, Summable (fun i => |w i * logKernel (a i) (gamma i) t|)) ∧
    Continuous (defect w a gamma) ∧
    (∀ T : ℝ, 0 ≤ T →
      R.readout () () (integratedDefect w a gamma T)
        (∑' i, w i * endpointKernel (a i) (gamma i) T)) ∧
    (∀ T : ℝ, 0 ≤ T → 0 ≤ integratedDefect w a gamma T) ∧
    (∀ T : ℝ, 0 < T →
      (0 < integratedDefect w a gamma T ↔ ∃ i, 0 < w i ∧ 0 < a i)) ∧
    Tendsto (fun T : ℝ => ENNReal.ofReal (T * integratedDefect w a gamma T)) atTop
      (𝓝 (2 * ∑' i, ENNReal.ofReal (w i * (a i)^2))) ∧
    (Tendsto (fun T : ℝ => T * integratedDefect w a gamma T) atTop (𝓝 0) ↔
      ∀ i, 0 < w i → a i = 0)

-- A whole-family counterfactual: the same zero-weight singleton data satisfy
-- every original premise, but the altered endpoint identity is False at T = 0.
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := @h (ULift.{u} Unit) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ)) (by intro i; norm_num) (by intro i; norm_num)
    (by intro i; norm_num) (by intro i; norm_num) (by simp)
  exact hbad.2.2.2.2.1 0 le_rfl

-- Actual equality distinguishes the real states 0 and 1, by evaluation at 0.
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℝ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero hh

def source_registration : Registration arena.{u}
    (type_of% @_root_.D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment.integrated_transverse_moment.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment.integrated_transverse_moment.{u},
    rejected, rejected_law⟩
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
      (@_root_.D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment.integrated_transverse_moment.{u})
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment.integrated_transverse_moment.unit
  realizationName := `Reg.D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment.integrated_transverse_moment.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end integrated_transverse_moment
end Reg.D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment
