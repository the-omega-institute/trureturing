import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.WeightedTail.RobinLogClockWeightedTail
import Reg.D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
import Reg.Support.SingleDependentReadout

/-! The strict comparison observes the integer's actual Robin log margin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open _root_.D5.S3.Arith.Robin.WeightedTail.RobinLogClockWeightedTail (weightedTail_lt_robinLogMargin)
open _root_.D5.S3.Weil.Mertens.WeightedTailTransport (weightedTail)
open _root_.D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open _root_.Reg.D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (signature actual family)

namespace Reg.D5.S3.Arith.Robin.WeightedTail.RobinLogClockWeightedTail

private def rejected : Realization signature :=
  realize signature (fun _ _ n => weightedTail psiErrorKernel (Real.log (n : ℝ)))
    (fun impossible => nomatch impossible)

def arena : Arena where
  signature := signature
  Law V := ∀ {n : ℕ}, 5040 < n →
    weightedTail psiErrorKernel (Real.log (n : ℝ)) < V.readout () () n

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  exact (lt_irrefl _) (h (n := 5041) (by norm_num))

def evidence : Registration arena (type_of% @weightedTail_lt_robinLogMargin) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weightedTail_lt_robinLogMargin, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := family.dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weightedTail_lt_robinLogMargin) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.WeightedTail.RobinLogClockWeightedTail.weightedTail_lt_robinLogMargin.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.WeightedTail.RobinLogClockWeightedTail.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout :=
    some (realize signature (fun _ _ n => robinLogMargin n) (fun impossible => nomatch impossible))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.WeightedTail.RobinLogClockWeightedTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Arith.Robin.WeightedTail.RobinLogClockWeightedTail
end
