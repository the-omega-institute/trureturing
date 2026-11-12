import D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- RegUNVALIDATED / UNCOMPILED_UNACCEPTED. Full-telescope typed ATTEMPTS only.
For EVERY target below:
 escapeFrom: named literal source readout; compiled occurrence binding is pending.
 readout: typed actual realization; lawful enrollment and sourceSelection are pending.
 realization: ENTIRE original telescope, actual_law, definitional source_bridge;
 rejected lawful families, whole-family intervention, other-readout/anchor-fixed
 sensitivity, actual observational dependence and axiom closure remain missing.
 continuation: unknown. No registration, binding or validation is asserted. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve
open Real Filter Finset
open scoped Topology BigOperators
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
open _root_.D5.S3.Arith.Robin.PriceRecord.UniformThetaShellError
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit


namespace budget_prefix_deletion_reserve
/- Source readout: real-endpoint theta in the exact deletion ledger. RegUNVALIDATED. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Chebyshev.theta x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧
      ∀ X : ℝ, T ≤ X → ∀ b : Budget, b.spec X →
      ∀ M : ℕ, (M : ℝ) ≤ C * log X →
        ∃ Q : ℕ, ∃ D : Finset ℕ, Q.Prime ∧ X / 2 < (Q : ℝ) ∧ Q ≤ b.Q ∧
          D = Nat.primesLE b.Q \ Nat.primesLE Q ∧ D.card = M ∧
          (∀ p ∈ D, p.Prime ∧ Q < p ∧ p ≤ b.Q) ∧
          (V.readout () ()) (b.Q : ℝ) - (V.readout () ()) (Q : ℝ) = ∑ p ∈ D, log p ∧
          (∑ p ∈ D, log p) ≤ (M : ℝ) * log (2 * X)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve.budget_prefix_deletion_reserve

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve.budget_prefix_deletion_reserve)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end budget_prefix_deletion_reserve

namespace finite_prefix_deletion_cost
/- Source readout: complete first-layer loss. RegUNVALIDATED. -/
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
  Law V := ∀ {X : ℝ} (hX : 4 < X)
    (b : Budget) (hb : b.spec X) {Q k M : ℕ}
    (hk : 2 ≤ k) (hkp : k.primeFactors = Nat.primesLE Q)
    (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X)) (hQb : Q ≤ b.Q)
    (D : Finset ℕ) (hD : D = Nat.primesLE b.Q \ Nat.primesLE Q) (hDM : D.card = M),
    |(V.readout ()) X k - (V.readout ()) X b.k| ≤
      6 * (shellError X + 3 * sqrt X + (M : ℝ) * log (2 * X) + 1) *
        ((M : ℝ) * log (2 * X)) / (X ^ 2 * log (X / 2)) ∧
    (∀ f : ℝ, (Q : ℝ) ≤ f → f ≤ b.Q →
      |log f - log X| ≤ (2 / X) *
        (shellError X + 3 * sqrt X + (M : ℝ) * log (2 * X)))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve.finite_prefix_deletion_cost

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve.finite_prefix_deletion_cost)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end finite_prefix_deletion_cost

end Reg.D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve

/- SOURCE ONLY. RegUNVALIDATED / UNCOMPILED_UNACCEPTED.
These are full-telescope typed ATTEMPTS, not registrations or validation.
Actual arithmetic realization, actual_law and definitional source_bridge are
provided. Compiled occurrence/sourceSelection binding, lawful enrollment,
rejected lawful families, whole-family intervention and realizability,
anchor/other-readout-fixed sensitivity, actual observational dependence and
axiom closure are UNKNOWN. No .unknown object closes a source proof gap. -/
namespace Reg.D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve.CurvatureConsumed
open Real Filter Finset
open scoped Topology BigOperators
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
open _root_.D5.S3.Arith.Robin.PriceRecord.UniformThetaShellError
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace budget_prefix_deletion_reserve_power
/- RegUNVALIDATED. Readout: actual theta difference. Full dependent telescope below. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => Chebyshev.theta t) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (d : ℕ),
    ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧
      ∀ X : ℝ, T ≤ X → ∀ b : Budget, b.spec X →
      ∀ M : ℕ, (M : ℝ) ≤ C * log X ^ d →
        ∃ Q : ℕ, ∃ D : Finset ℕ, Q.Prime ∧ X / 2 < (Q : ℝ) ∧ Q ≤ b.Q ∧
          D = Nat.primesLE b.Q \ Nat.primesLE Q ∧ D.card = M ∧
          (∀ p ∈ D, p.Prime ∧ Q < p ∧ p ≤ b.Q) ∧
          ((V.readout ()) () (b.Q : ℝ)) - ((V.readout ()) () (Q : ℝ)) = ∑ p ∈ D, log p ∧
          (∑ p ∈ D, log p) ≤ (M : ℝ) * log (2 * X)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve.budget_prefix_deletion_reserve_power

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve.budget_prefix_deletion_reserve_power)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end budget_prefix_deletion_reserve_power

end Reg.D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve.CurvatureConsumed
