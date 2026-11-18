import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionArithmetic
import D5.S3.Arith.Robin.Analytic.ExceptionCount.MertensGap
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Real LeanInformationAudit
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion
open _root_.D5.S3.Arith.Robin.Analytic.ExceptionCount
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionArithmetic

namespace Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionArithmetic

namespace Robin

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P : ℝ}, 1 < P → ∀ {n : ℕ}, n ≠ 0 →
    n.primeFactors.card ≤ Nat.primeCounting ⌊P⌋₊ →
    R.readout () () ((ArithmeticFunction.sigma 1 n : ℝ) / n) (MertensGap.product P)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 2) (by norm_num) (n := 1) (by norm_num) (by simp)

def family : Registration arena (type_of% @robin_product_upper) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@robin_product_upper, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@robin_product_upper) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionArithmetic.robin_product_upper.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionArithmetic.Robin.family
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
    owner := `D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionArithmetic
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

end Robin


namespace Kappa

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {delta : ℝ}, 0 < delta → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (κ P : ℝ) (n : ℕ), 1 + delta ≤ κ → 2 ≤ P → n ≠ 0 →
      n.primeFactors.card ≤ Nat.primeCounting ⌊P⌋₊ →
      R.readout () ()
        ((riemannZeta (κ : ℂ)).re * sigmaKappa κ n / (n : ℝ) ^ κ)
        ((MertensGap.product P * exp (C * P ^ (-(delta / 2)))) ^ κ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨C, hC, hh⟩ := h (delta := 1) (by norm_num)
  exact hh 2 2 1 (by norm_num) (by norm_num) (by norm_num) (by simp)

def family : Registration arena (type_of% @kappa_product_tail_upper) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kappa_product_tail_upper, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kappa_product_tail_upper) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionArithmetic.kappa_product_tail_upper.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionArithmetic.Kappa.family
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
    owner := `D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionArithmetic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Kappa

end Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionArithmetic
