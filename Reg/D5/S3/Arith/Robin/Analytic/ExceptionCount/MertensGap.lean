import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.ExceptionCount.MertensGap
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.ExceptionCount.MertensGap
open _root_.D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff

namespace Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.MertensGap

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {a : ℝ}, 0 < a → ∀ C : ℝ, ∀ᶠ x : ℝ in atTop,
    R.readout () ()
      (product (cutoff (log (log x))) * exp (C * (cutoff (log (log x))) ^ (-a)))
      (exp eulerMascheroniConstant * log (log (x / 2)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh : ∀ᶠ x : ℝ in atTop, False := h (a := 1) (by norm_num) 0
  obtain ⟨x, hx⟩ := hh.exists
  exact hx

def family : Registration arena (type_of% @upper_half_product_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@upper_half_product_gap, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) (by norm_num : (0 : ℝ) < 1)
    exact lt_irrefl _ hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@upper_half_product_gap) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ExceptionCount.MertensGap.upper_half_product_gap.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.MertensGap.family
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
    owner := `D5.S3.Arith.Robin.Analytic.ExceptionCount.MertensGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.MertensGap
