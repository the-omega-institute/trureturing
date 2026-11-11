import D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget
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
namespace Reg.D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget
open Real Filter Finset
open scoped Topology BigOperators
open _root_.D5.S3.Constants.Irrationality.LogPrimeRatioIrrationality
open _root_.D5.S3.Diophantine.StablePositiveSemigroup
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (firstLayerPrice)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace seeded_two_layer_coefficients
/- Source readout: actual real beta cutoff. RegUNVALIDATED. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ j x => cutoff j x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, ∃ C T : ℝ, 0 < C ∧ 1 < T ∧
      ∀ X : ℝ, T ≤ X → ∀ δ₀ f : ℝ,
        0 ≤ δ₀ → δ₀ ≤ log (2 * X) → f ∈ Set.Icc (X / 2) (2 * X) →
        ∃ a b : ℕ, b ≤ B ∧ (a + b : ℝ) ≤ C * log X ∧
          log X - log 2 ≤ δ₀ + log f ∧
          δ₀ + log f ≤ 2 * log X + 2 * log 2 ∧
          δ₀ + log f - ε / 2 ≤
            (a : ℝ) * (2 * log ((V.readout ()) 2 (referencePrice X)) - log X) +
            (b : ℝ) * (3 * log ((V.readout ()) 3 (referencePrice X)) - log X) ∧
          (a : ℝ) * (2 * log ((V.readout ()) 2 (referencePrice X)) - log X) +
            (b : ℝ) * (3 * log ((V.readout ()) 3 (referencePrice X)) - log X) ≤
              δ₀ + log f - ε / 4

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget.seeded_two_layer_coefficients

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget.seeded_two_layer_coefficients)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end seeded_two_layer_coefficients

namespace two_roster_integer_ledger
/- Source readout: total actual defect in the entire source telescope. RegUNVALIDATED. -/
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
  realize signature (fun _ X n => actualDefect X n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {X : ℝ} (hX : 4 < X) {Q : ℕ}
    (hQ2 : 2 ≤ Q) (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    {r : ℝ} (hr : r ∈ Set.Icc (X / 2) (2 * X))
    (hroot : firstLayerPrice r = referencePrice X)
    (hsupport : ∀ p : ℕ, p.Prime →
      2 ≤ (strictInteger (referencePrice X)).factorization p → p ≤ Q)
    (A₂ A₃ : Finset ℕ) (hdis : Disjoint A₂ A₃)
    (hA₂ : ∀ p ∈ A₂, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = 1)
    (hA₃ : ∀ p ∈ A₃, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = 2),
    let n := strictInteger (referencePrice X)
    let base := higherCore n * prefixInteger Q
    let k := base * (∏ p ∈ A₂, p) * (∏ p ∈ A₃, p)
    2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧
      (∀ p : ℕ, k.factorization p =
        base.factorization p + (if p ∈ A₂ then 1 else 0) + (if p ∈ A₃ then 1 else 0)) ∧
      log (k : ℝ) = log (higherCore n : ℝ) + Chebyshev.theta (Q : ℝ) +
        (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧
      log (higherCore k : ℝ) = log (higherCore n : ℝ) +
        (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧
      (V.readout ()) X k - completeFirstLayerLoss X k =
        (∑ p ∈ A₂, (referencePrice X - goldenLayerMarginal p 2) * log p) +
        (∑ p ∈ A₃, (referencePrice X - goldenLayerMarginal p 3) * log p) ∧
      (∀ p : ℕ, p.Prime → p ∉ A₂ ∪ A₃ → ∀ j : ℕ, 2 ≤ j →
        (j ≤ k.factorization p ↔ j ≤ optimalLayerCount (referencePrice X) p))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget.two_roster_integer_ledger

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget.two_roster_integer_ledger)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end two_roster_integer_ledger

namespace finite_paid_prefix_comparison
/- Source readout: total actual defect in the entire source telescope. RegUNVALIDATED. -/
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
  realize signature (fun _ X n => actualDefect X n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {η X μ : ℝ} (hX : 4 < X)
    {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k) (hμ : 0 < μ)
    (hrecord : ∀ a : ℕ, 0 < a → a < m →
      goldenResourceObjective μ a < goldenResourceObjective μ m)
    (hclock : X = log (m : ℝ))
    (hP : (largestPrime m : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    (b : Budget) (hb : b.spec X)
    (hslack : 0 ≤ X - log (k : ℝ))
    (hpaid : |completeFirstLayerLoss X k - completeFirstLayerLoss X b.k| +
      ((V.readout ()) X k - completeFirstLayerLoss X k) +
        referencePrice X * (X - log (k : ℝ)) ≤ η / (X * log X)),
    k ≤ m ∧ 0 ≤ (V.readout ()) X m - completeFirstLayerLoss X m ∧
      (V.readout ()) X m - completeFirstLayerLoss X m + μ * (X - log (k : ℝ)) ≤
        η / (X * log X) +
        6 * max (|(largestPrime m : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) *
          |b.h + b.δ - (log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ))| /
            (X ^ 2 * log (X / 2))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget.finite_paid_prefix_comparison

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget.finite_paid_prefix_comparison)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end finite_paid_prefix_comparison

namespace residual_nonneg
/- Source readout: total actual defect in the entire source telescope. RegUNVALIDATED. -/
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
  realize signature (fun _ X n => actualDefect X n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {X : ℝ} (hX : 1 < X) {n : ℕ} (hn : 1 ≤ n),
    0 ≤ (V.readout ()) X n - completeFirstLayerLoss X n

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair.residual_nonneg

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair.residual_nonneg)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end residual_nonneg

namespace insert_roster_at_prefix
/- Source readout: total actual defect in the entire source telescope. RegUNVALIDATED. -/
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
  realize signature (fun _ X n => actualDefect X n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {X : ℝ} (hX : 4 < X) {base Q : ℕ}
    (hb2 : 2 ≤ base) (hpref : base.primeFactors = Nat.primesLE Q)
    (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X)) {r : ℝ}
    (hr : r ∈ Set.Icc (X / 2) (2 * X))
    (hroot : firstLayerPrice r = referencePrice X)
    {J : ℕ} (hJ : 1 ≤ J) (A : Finset ℕ)
    (hA : ∀ p ∈ A, p.Prime ∧ p ≤ Q ∧ base.factorization p = J - 1),
    let k := base * ∏ p ∈ A, p
    2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧
      log (k : ℝ) - log (base : ℝ) = ∑ p ∈ A, log p ∧
      (∀ p, k.factorization p = base.factorization p + if p ∈ A then 1 else 0) ∧
      (V.readout ()) X k - completeFirstLayerLoss X k =
        ((V.readout ()) X base - completeFirstLayerLoss X base) +
          ∑ p ∈ A, (referencePrice X - goldenLayerMarginal p J) * log p

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair.insert_roster_at_prefix

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair.insert_roster_at_prefix)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end insert_roster_at_prefix

namespace two_price_compare
/- Source readout: total actual defect in the entire source telescope. RegUNVALIDATED. -/
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
  realize signature (fun _ X n => actualDefect X n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {X μ : ℝ} {m k : ℕ}
    (hm : 2 ≤ m) (hk : 2 ≤ k) (hμ : 0 < μ)
    (hrecord : ∀ a : ℕ, 0 < a → a < m →
      goldenResourceObjective μ a < goldenResourceObjective μ m)
    (hclock : X = log (m : ℝ)) (hslack : 0 ≤ X - log (k : ℝ)),
    k ≤ m ∧ (V.readout ()) X m - (V.readout ()) X k ≤
      (referencePrice X - μ) * (X - log (k : ℝ))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair.two_price_compare

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair.two_price_compare)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end two_price_compare

namespace prefix_budget_integer
/- Source readout: natural higher core including its occurrence in the constructed integer. RegUNVALIDATED. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => higherCore n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {n Q : ℕ} (hQ : 2 ≤ Q)
    (hsupport : ∀ p : ℕ, p.Prime → 2 ≤ n.factorization p → p ≤ Q),
    let k := (V.readout () ()) n * prefixInteger Q
    2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧
    log (k : ℝ) = log ((V.readout () ()) n : ℝ) + Chebyshev.theta (Q : ℝ) ∧
    ∀ p : ℕ, p.Prime → ∀ j : ℕ, 2 ≤ j →
      (j ≤ k.factorization p ↔ j ≤ n.factorization p)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder.prefix_budget_integer

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder.prefix_budget_integer)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end prefix_budget_integer

end Reg.D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget

/- SOURCE ONLY. RegUNVALIDATED / UNCOMPILED_UNACCEPTED.
These are full-telescope typed ATTEMPTS, not registrations or validation.
Actual arithmetic realization, actual_law and definitional source_bridge are
provided. Compiled occurrence/sourceSelection binding, lawful enrollment,
rejected lawful families, whole-family intervention and realizability,
anchor/other-readout-fixed sensitivity, actual observational dependence and
axiom closure are UNKNOWN. No .unknown object closes a source proof gap. -/
namespace Reg.D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget.CurvatureConsumed
open Real Filter Finset
open scoped Topology BigOperators
open _root_.D5.S3.Constants.Irrationality.LogPrimeRatioIrrationality
open _root_.D5.S3.Diophantine.StablePositiveSemigroup
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualHigherLayerBudgetRepair
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (firstLayerPrice)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace two_roster_integer_ledger_at_layers
/- RegUNVALIDATED. Readout: actual natural factorization. Full dependent telescope below. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n p => n.factorization p) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j)
    {X : ℝ} (hX : 4 < X) {Q : ℕ}
    (hQ2 : 2 ≤ Q) (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    {r : ℝ} (hr : r ∈ Set.Icc (X / 2) (2 * X))
    (hroot : firstLayerPrice r = referencePrice X)
    (hsupport : ∀ p : ℕ, p.Prime →
      2 ≤ (strictInteger (referencePrice X)).factorization p → p ≤ Q)
    (A₂ A₃ : Finset ℕ) (hdis : Disjoint A₂ A₃)
    (hA₂ : ∀ p ∈ A₂, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = i - 1)
    (hA₃ : ∀ p ∈ A₃, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = j - 1),
    let n := strictInteger (referencePrice X)
    let base := higherCore n * prefixInteger Q
    let k := base * (∏ p ∈ A₂, p) * (∏ p ∈ A₃, p)
    2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧
      (∀ p : ℕ, ((V.readout ()) k p) =
        ((V.readout ()) base p) + (if p ∈ A₂ then 1 else 0) + (if p ∈ A₃ then 1 else 0)) ∧
      log (k : ℝ) = log (higherCore n : ℝ) + Chebyshev.theta (Q : ℝ) +
        (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧
      log (higherCore k : ℝ) = log (higherCore n : ℝ) +
        (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧
      actualDefect X k - completeFirstLayerLoss X k =
        (∑ p ∈ A₂, (referencePrice X - goldenLayerMarginal p i) * log p) +
        (∑ p ∈ A₃, (referencePrice X - goldenLayerMarginal p j) * log p) ∧
      (∀ p : ℕ, p.Prime → p ∉ A₂ ∪ A₃ → ∀ l : ℕ, 2 ≤ l →
        (l ≤ ((V.readout ()) k p) ↔ l ≤ optimalLayerCount (referencePrice X) p))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget.two_roster_integer_ledger_at_layers

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget.two_roster_integer_ledger_at_layers)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end two_roster_integer_ledger_at_layers

end Reg.D5.S3.Arith.Robin.PriceRecord.TwoFixedLayerPrefixBudget.CurvatureConsumed
