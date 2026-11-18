import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaSecond.ContinuumWeight
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real MeasureTheory Set LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.ContinuumWeight

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.ContinuumWeight



namespace CentralIntegral

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P s : ℝ}, 0 < P → 1 < s →
    R.readout () () (∫ t in (P / 2)..(2 * P), MovingWeight.weight P s t)
      (P * (π / sin (π / s) - s) + (s / 2 + 2) * P * (2 : ℝ) ^ (-s))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 2) (by norm_num) (by norm_num)

def family : Registration arena (type_of% @central_integral_upper) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@central_integral_upper, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@central_integral_upper) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.ContinuumWeight.central_integral_upper.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.ContinuumWeight.CentralIntegral.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.ContinuumWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CentralIntegral

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.ContinuumWeight
