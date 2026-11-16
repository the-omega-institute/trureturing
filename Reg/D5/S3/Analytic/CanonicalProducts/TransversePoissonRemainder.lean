import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder
import Reg.Support.DependentFamily

/-! Full-source family observing the signed lower fourth-order remainder bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open _root_.D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder
namespace integrated_defect_poisson_remainder

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
  Law R := ∀ {I : Type u} (w a gamma : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1 / 2)
    (hgamma : ∀ i, 0 < gamma i)
    (hbudget : Summable (fun i => w i * (a i)^2 / (gamma i)^2))
    (T : ℝ) (hT : 1 ≤ T),
    Summable (fun i => w i * (a i)^4 * T / (T^2 + (gamma i)^2)^2) ∧
    R.readout () ()
      (-(∑' i, w i * (a i)^4 * T / (T^2 + (gamma i)^2)^2))
      (integratedDefect w a gamma T -
        2 * (∑' i, w i * (a i)^2 * T / (T^2 + (gamma i)^2))) ∧
    integratedDefect w a gamma T -
        2 * (∑' i, w i * (a i)^2 * T / (T^2 + (gamma i)^2)) ≤
      (4 / 9 : ℝ) * (∑' i, w i * (a i)^4 * T / (T^2 + (gamma i)^2)^2) ∧
    (∑' i, w i * (a i)^4 * T / (T^2 + (gamma i)^2)^2) ≤
      (∑' i, w i * (a i)^2 * T / (T^2 + (gamma i)^2)) / (4 * T^2)

-- Zero weights on a singleton satisfy every premise; the altered lower bound is False.
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := @h (ULift.{u} Unit) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ)) (by intro i; norm_num) (by intro i; norm_num)
    (by intro i; norm_num) (by intro i; norm_num) (by simp) 1 le_rfl
  exact hbad.2.1

-- The actual order readout distinguishes the real states 0 and 1 at output 0.
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  exact (not_le_of_gt zero_lt_one) hh

def source_registration : Registration arena.{u}
    (type_of% @_root_.D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder.integrated_defect_poisson_remainder.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder.integrated_defect_poisson_remainder.{u},
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
      (@_root_.D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder.integrated_defect_poisson_remainder.{u})
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder.integrated_defect_poisson_remainder.unit
  realizationName := `Reg.D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder.integrated_defect_poisson_remainder.source_registration
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
    owner := `D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end integrated_defect_poisson_remainder
end Reg.D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder
