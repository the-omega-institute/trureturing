import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.RobinExceptionCount
import Reg.Support.SingleDependentReadout

/-! Typed source families for the two Robin exception-count bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion
open _root_.D5.S3.Arith.Robin.Analytic.RobinExceptionCount

namespace Reg.D5.S3.Arith.Robin.Analytic.RobinExceptionCount
namespace KappaCount

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {delta epsilon : ℝ}, 0 < delta → 0 < epsilon →
    ∀ᶠ x : ℝ in atTop,
      R.readout () ()
        (((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 2162160 < n ∧
          ∃ κ : ℝ, 1 + delta ≤ κ ∧
            (exp eulerMascheroniConstant * n * log (log n)) ^ κ ≤
              (riemannZeta (κ : ℂ)).re * sigmaKappa κ n)).card : ℝ)
        (exp ((C0 + epsilon) * scale x))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfalse := h (delta := 1) (epsilon := 1) (by norm_num) (by norm_num)
  obtain ⟨x, hx⟩ := hfalse.exists
  exact hx

def family : Registration arena (type_of% @kappa_exception_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kappa_exception_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

/- The four-slot audit of kappa_exception_count is incomplete; see issue #31382. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kappa_exception_count) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.RobinExceptionCount.kappa_exception_count.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.RobinExceptionCount.KappaCount.family
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
    owner := `D5.S3.Arith.Robin.Analytic.RobinExceptionCount
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end KappaCount

namespace RobinCount

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {epsilon : ℝ}, 0 < epsilon →
    ∀ᶠ x : ℝ in atTop,
      R.readout () ()
        (((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 5040 < n ∧
          exp eulerMascheroniConstant * n * log (log n) ≤
            (ArithmeticFunction.sigma 1 n : ℝ))).card : ℝ)
        (exp ((C0 + epsilon) * scale x))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfalse := h (epsilon := 1) (by norm_num)
  obtain ⟨x, hx⟩ := hfalse.exists
  exact hx

def family : Registration arena (type_of% @robin_exception_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@robin_exception_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

/- The four-slot audit of robin_exception_count is incomplete; see issue #31382. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@robin_exception_count) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.RobinExceptionCount.robin_exception_count.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.RobinExceptionCount.RobinCount.family
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
    owner := `D5.S3.Arith.Robin.Analytic.RobinExceptionCount
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RobinCount

end Reg.D5.S3.Arith.Robin.Analytic.RobinExceptionCount
