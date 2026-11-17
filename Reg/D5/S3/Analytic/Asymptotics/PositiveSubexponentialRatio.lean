import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio
import Reg.Support.DependentFamily

/-! Source-bound interventions on actual comparisons, equality or product convergence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

open Filter
open scoped BigOperators Topology
open _root_.D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio

namespace linear_exponent_eq_zero

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
  Law R := ∀ (a b : ℂ) (p q : ℝ → ℝ)
    (hp : ∀ᶠ x : ℝ in atTop, 0 < p x)
    (hq : ∀ᶠ x : ℝ in atTop, 0 < q x)
    (hlogp : Tendsto (fun x : ℝ => Real.log (p x) / x) atTop (𝓝 0))
    (hlogq : Tendsto (fun x : ℝ => Real.log (q x) / x) atTop (𝓝 0))
    (hlim : Tendsto
      (fun x : ℝ => Complex.exp (a * (x : ℂ) + b) * (p x : ℂ) / (q x : ℂ))
      atTop (𝓝 1)),
    R.readout () () a 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 (fun _ => 1) (fun _ => 1) (by simp) (by simp)
    (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)))
    (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)))
    (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (𝓝 1)))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : (1 : ℂ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero hh

def source_registration : Registration arena (type_of% @_root_.D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio.linear_exponent_eq_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio.linear_exponent_eq_zero, rejected, rejected_law⟩
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
      (@_root_.D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio.linear_exponent_eq_zero) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio.linear_exponent_eq_zero.unit
  realizationName := `Reg.D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio.linear_exponent_eq_zero.source_registration
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
    owner := `D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end linear_exponent_eq_zero

end Reg.D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio
