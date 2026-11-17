import D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- RegUNVALIDATED source attempts; UNCOMPILED_UNACCEPTED. No Contract.Registration
   or DependentFamily.Registration is asserted. The candidate full-law attempts
   below retain the complete original telescope and use literal arithmetic readouts.
   actual_law and source_bridge are uncompiled attempts, not binding evidence.
   No sourceSelection coordinates, variation, sensitivity, observational dependence,
   enrolled application certificate, native report or declared_validated status is supplied.
   Linked-issue disclosure remains for the later authorized native/publication owner. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation

open Finset Real
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity
  (block mem_block first_margin positive_margin_mem)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (firstLayerPrice)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace complete_first_layer_prefix_cancellation

/- Four-slot attempt for D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation.complete_first_layer_prefix_cancellation:
   escapeFrom: the literal operand completeFirstLayerLoss in the original statement;
     no compiler source-occurrence/binder identity is asserted.
   readout: DependentFamily.realize with the literal family below; exact enrolled
     readout/sourceSelection reconstruction and current binding evidence are missing.
   realization: full original law and definitional bridge attempted below; rejected
     lawful-domain family, whole-family variation, sensitivity with other slots fixed,
     and actual observational dependence remain unproved.
   continuation: unknown only; no residual witness, emptiness or undecidability claim.
   This is an unfinished source attempt, not a valid four-slot registration. -/

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ X n => completeFirstLayerLoss X n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {X r : ℝ} (hX : 4 < X)
      {m k P Q : ℕ}
      (hmprefix : m.primeFactors = Nat.primesLE P)
      (hkprefix : k.primeFactors = Nat.primesLE Q)
      (hP : (P : ℝ) ∈ Set.Icc (X / 2) (2 * X))
      (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X))
      (hr : r ∈ Set.Icc (X / 2) (2 * X))
      (hroot : firstLayerPrice r = referencePrice X),
      |V.readout () X k - V.readout () X m| ≤
        6 * max (|(P : ℝ) - r|) (|(Q : ℝ) - r|) *
          |Chebyshev.theta (P : ℝ) - Chebyshev.theta (Q : ℝ)| /
            (X ^ 2 * log (X / 2))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation.complete_first_layer_prefix_cancellation

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation.complete_first_layer_prefix_cancellation)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge

end complete_first_layer_prefix_cancellation

namespace actual_record_prefix_budget_residual

/- Four-slot attempt for D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation.actual_record_prefix_budget_residual:
   escapeFrom: the literal operand actualDefect X m - completeFirstLayerLoss X m in the original statement;
     no compiler source-occurrence/binder identity is asserted.
   readout: DependentFamily.realize with the literal family below; exact enrolled
     readout/sourceSelection reconstruction and current binding evidence are missing.
   realization: full original law and definitional bridge attempted below; rejected
     lawful-domain family, whole-family variation, sensitivity with other slots fixed,
     and actual observational dependence remain unproved.
   continuation: unknown only; no residual witness, emptiness or undecidability claim.
   This is an unfinished source attempt, not a valid four-slot registration. -/

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ X m => actualDefect X m - completeFirstLayerLoss X m) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {X r δ mu : ℝ} {m k P Q : ℕ}
      (hX : 4 < X) (hm : 2 ≤ m) (hk : 2 ≤ k) (hmu : 0 < mu)
      (hrecord : ∀ a : ℕ, 0 < a → a < m →
        goldenResourceObjective mu a < goldenResourceObjective mu m)
      (hclock : X = log (m : ℝ))
      (hmprefix : m.primeFactors = Nat.primesLE P)
      (hkprefix : k.primeFactors = Nat.primesLE Q)
      (hP : (P : ℝ) ∈ Set.Icc (X / 2) (2 * X))
      (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X))
      (hr : r ∈ Set.Icc (X / 2) (2 * X))
      (hroot : firstLayerPrice r = referencePrice X)
      (hδ : 0 ≤ δ) (hbudget : log (k : ℝ) + δ = X)
      (hhigher : ∀ p : ℕ, p.Prime → ∀ j : ℕ, 2 ≤ j →
        (j ≤ k.factorization p ↔ j ≤ optimalLayerCount (referencePrice X) p)),
      0 ≤ V.readout () X m ∧
      V.readout () X m ≤
        6 * max (|(P : ℝ) - r|) (|(Q : ℝ) - r|) *
          |Chebyshev.theta (P : ℝ) - Chebyshev.theta (Q : ℝ)| /
            (X ^ 2 * log (X / 2)) + δ / (X * log X)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation.actual_record_prefix_budget_residual

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation.actual_record_prefix_budget_residual)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge

end actual_record_prefix_budget_residual

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation

/- SOURCE ONLY. RegUNVALIDATED / UNCOMPILED_UNACCEPTED.
These are full-telescope typed ATTEMPTS, not registrations or validation.
Actual arithmetic realization, actual_law and definitional source_bridge are
provided. Compiled occurrence/sourceSelection binding, lawful enrollment,
rejected lawful families, whole-family intervention and realizability,
anchor/other-readout-fixed sensitivity, actual observational dependence and
axiom closure are UNKNOWN. No .unknown object closes a source proof gap. -/
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation.CurvatureConsumed
open Finset Real
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity
  (block mem_block first_margin positive_margin_mem)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (firstLayerPrice)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace ordered_prefix_difference
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
  Law V := ∀ {X : ℝ} (hX : 1 < X)
    {m k P Q : ℕ} (hmprefix : m.primeFactors = Nat.primesLE P)
    (hkprefix : k.primeFactors = Nat.primesLE Q) (hPQ : P ≤ Q),
    ((V.readout (0 : Fin 2)) X k) - ((V.readout (0 : Fin 2)) X m) =
      -(∑ p ∈ block (P : ℝ) Q, rawLayerMargin X p 1)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation.ordered_prefix_difference

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation.ordered_prefix_difference)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end ordered_prefix_difference

namespace raw_first_bound_at_root
/- RegUNVALIDATED. Readout: actual signed first margin. Full dependent telescope below. -/
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ X t => log (1 + 1 / t) - log t / (X * log X)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {X r t : ℝ} (hX : 4 < X)
    (hr : r ∈ Set.Icc (X / 2) (2 * X))
    (hroot : firstLayerPrice r = referencePrice X)
    (ht : t ∈ Set.Icc (X / 2) (2 * X)),
    |((V.readout ()) X t)| ≤ (6 / X ^ 2) * |t - r|

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation.raw_first_bound_at_root

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation.raw_first_bound_at_root)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end raw_first_bound_at_root

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation.CurvatureConsumed
