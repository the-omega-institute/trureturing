import D5.S3.Arith.Robin.PriceRecord.ActualTwoFourPaidPrefixRepair
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/- SOURCE ONLY. RegUNVALIDATED / UNCOMPILED_UNACCEPTED.
These are full-telescope typed ATTEMPTS, not registrations or validation.
Actual arithmetic realization, actual_law and definitional source_bridge are
provided. Compiled occurrence/sourceSelection binding, lawful enrollment,
rejected lawful families, whole-family intervention and realizability,
anchor/other-readout-fixed sensitivity, actual observational dependence and
axiom closure are UNKNOWN. No .unknown object closes a source proof gap. -/
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourPaidPrefixRepair.CurvatureConsumed
open Real Filter Finset
open scoped Topology BigOperators
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
open _root_.D5.S3.Arith.Robin.PriceRecord.PositiveCurvatureFloorMesh
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity (block first_margin)
open _root_.D5.S3.Arith.Robin.PriceRecord.UniformThetaShellError
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open _root_.D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerInsertionRegret
open _root_.D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerQuantitativeBudgetRepair
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace actual_two_four_paid_prefix_repair
/- RegUNVALIDATED. Readout: actual complete first loss and full defect. Full dependent telescope below. -/
abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun r X n => if r = 0 then completeFirstLayerLoss X n else actualDefect X n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∃ X0 : ℝ, 1 < X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ b : Budget, b.spec X → ∃ k Qprime : ℕ,
        2 ≤ k ∧ Qprime.Prime ∧ X / 2 < (Qprime : ℝ) ∧ (Qprime : ℝ) ≤ 2 * X ∧
        k.primeFactors = Nat.primesLE Qprime ∧ log (k : ℝ) < X ∧
        |((V.readout (0 : Fin 2)) X k) - ((V.readout (0 : Fin 2)) X b.k)| +
          (((V.readout (1 : Fin 2)) X k) - ((V.readout (0 : Fin 2)) X k)) +
          referencePrice X * (X - log (k : ℝ)) ≤ 10 / (X * log X ^ 3)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourPaidPrefixRepair.actual_two_four_paid_prefix_repair

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourPaidPrefixRepair.actual_two_four_paid_prefix_repair)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end actual_two_four_paid_prefix_repair

namespace canonical_paid_prefix_budget_eventually
/- RegUNVALIDATED. Readout: actual complete first loss and full defect. Full dependent telescope below. -/
abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun r X n => if r = 0 then completeFirstLayerLoss X n else actualDefect X n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∃ b : ℝ → Budget, ∀ᶠ X : ℝ in atTop, (b X).spec X ∧
      ∃ k Qprime : ℕ, 2 ≤ k ∧ Qprime.Prime ∧ X / 2 < (Qprime : ℝ) ∧
        (Qprime : ℝ) ≤ 2 * X ∧ k.primeFactors = Nat.primesLE Qprime ∧
        log (k : ℝ) < X ∧
        |((V.readout (0 : Fin 2)) X k) - ((V.readout (0 : Fin 2)) X (b X).k)| +
          (((V.readout (1 : Fin 2)) X k) - ((V.readout (0 : Fin 2)) X k)) +
          referencePrice X * (X - log (k : ℝ)) ≤ 10 / (X * log X ^ 3)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourPaidPrefixRepair.canonical_paid_prefix_budget_eventually

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourPaidPrefixRepair.canonical_paid_prefix_budget_eventually)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end canonical_paid_prefix_budget_eventually

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourPaidPrefixRepair.CurvatureConsumed
