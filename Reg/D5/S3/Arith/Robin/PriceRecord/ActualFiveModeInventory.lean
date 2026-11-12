import D5.S3.Arith.Robin.PriceRecord.ActualFiveModeInventory
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- Full-telescope actual laws and definitional source bridges.
Four-slot registration is unfinished: lawful enrolled-template application,
compiler occurrence/sourceSelection binding, whole-family intervention,
fixed-coordinate sensitivity and observational dependence remain unproved. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeInventory
open Real Filter Finset
open scoped Topology BigOperators
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace actual_high_inventory
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
  realize signature (fun _ p x => layerPrime p x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (hgap : BHPMaximumGap) (hcount : BHPShortIntervalCount)
    (j : ℕ) (hj : 2 ≤ j),
    ∃ A W T : ℝ, 0 < A ∧ 0 < W ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T ≤ (largestPrime m : ℝ) →
        let Q : ℝ := (V.readout ()) m j
        let R : ℝ := largestPrime m
        ∃ Lo Hi : Finset ℕ,
          Lo.card = comparisonCount j R ∧ Hi.card = comparisonCount j R ∧
          Disjoint Lo Hi ∧ R ≤ Q ^ j ∧ W * Q ^ bhpExponent ≤ Q / 2 ∧
          |beta j Q - beta 1 R| ≤ A * beta 1 R * R ^ (-priceExponent j) ∧
          (∀ p ∈ Lo, p.Prime ∧ 2 < p ∧ m.factorization p = j ∧
            Q - W * Q ^ bhpExponent ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q) ∧
          (∀ p ∈ Hi, p.Prime ∧ 2 < p ∧ m.factorization p = j - 1 ∧
            Q < (p : ℝ) ∧ (p : ℝ) ≤ Q + W * Q ^ bhpExponent)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.actual_high_inventory

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.actual_high_inventory)) ↔ arena.Law actual := Iff.rfl

end actual_high_inventory

namespace actual_first_inventory
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
  realize signature (fun _ _ x => largestPrime x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (hcount : BHPShortIntervalCount),
    ∃ W T : ℝ, 0 < W ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T ≤ ((V.readout () ()) m : ℝ) →
        let R : ℝ := (V.readout () ()) m
        ∃ Lo Hi : Finset ℕ,
          Lo.card = comparisonCount 16 R ∧ Hi.card = comparisonCount 16 R ∧
          Disjoint Lo Hi ∧ W * R ^ bhpExponent ≤ R / 2 ∧
          (∀ p ∈ Lo, p.Prime ∧ 2 < p ∧ m.factorization p = 1 ∧
            R - W * R ^ bhpExponent ≤ (p : ℝ) ∧ (p : ℝ) ≤ R) ∧
          (∀ p ∈ Hi, p.Prime ∧ 2 < p ∧ m.factorization p = 0 ∧
            R < (p : ℝ) ∧ (p : ℝ) ≤ R + W * R ^ bhpExponent)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.actual_first_inventory

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.actual_first_inventory)) ↔ arena.Law actual := Iff.rfl

end actual_first_inventory

namespace actual_finite_predecessor
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
  realize signature (fun _ p x => goldenResourceObjective p x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {m : ℕ} (hm : 2 ≤ m)
    {mu lambda : ℝ} (hmu : 0 < mu) (hrecord : FullRecord m mu)
    (D U : Finset ℕ)
    (hD : ∀ p ∈ D, p.Prime ∧ 2 < p ∧ p ∣ m)
    (hU : ∀ p ∈ U, p.Prime ∧ 2 < p)
    (hDU : Disjoint D U)
    (hmass : 0 < log 2 + logMass D - logMass U),
    ∃ n : ℕ, 0 < n ∧ n < m ∧
      log (m : ℝ) - log (n : ℝ) = log 2 + logMass D - logMass U ∧
      n.factorization 2 + 1 = m.factorization 2 ∧
      (V.readout ()) lambda n - (V.readout ()) lambda m =
        topGain lambda m + auxiliaryGain lambda m D U ∧
      topGain lambda m < (lambda - mu) * (log (m : ℝ) - log (n : ℝ)) -
        auxiliaryGain lambda m D U

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.actual_finite_predecessor

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.actual_finite_predecessor)) ↔ arena.Law actual := Iff.rfl

end actual_finite_predecessor

namespace uniform_actual_clock
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
  realize signature (fun _ _ x => largestPrime x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∃ T : ℝ, 0 < T ∧
    ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
      T ≤ ((V.readout () ()) m : ℝ) →
      1 ≤ log ((V.readout () ()) m : ℝ) ∧ 0 < log (log (m : ℝ)) ∧
      log ((V.readout () ()) m : ℝ) / 2 ≤ log (log (m : ℝ)) ∧
      log (log (m : ℝ)) ≤ 2 * log ((V.readout () ()) m : ℝ)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.uniform_actual_clock

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.uniform_actual_clock)) ↔ arena.Law actual := Iff.rfl

end uniform_actual_clock

namespace eventual_mass_error_absorption
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
  realize signature (fun _ _ x => mesh4 x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (K : ℝ) (hK : 0 ≤ K),
    ∀ᶠ X : ℝ in atTop,
      0 < (V.readout () ()) X ∧ K * log X * X ^ (-(19 / 640 : ℝ)) ≤ (V.readout () ()) X / 2

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.eventual_mass_error_absorption

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.eventual_mass_error_absorption)) ↔ arena.Law actual := Iff.rfl

end eventual_mass_error_absorption

namespace pointwise_boundary_estimates
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => goldenLayerMarginal p x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {j : ℕ} (hj : 1 ≤ j)
    {R Q W A H root : ℝ} (hR : 4 ≤ R) (hQ : 4 ≤ Q) (hQR : Q ≤ R)
    (hRQ : R ≤ Q ^ j) (hW : 0 ≤ W) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hlog : log R / (4 * (j : ℝ)) ≤ log (Q / 2))
    (hwidth : W * Q ^ bhpExponent ≤ Q / 2)
    (hband : |beta j Q - beta 1 R| ≤ A * beta 1 R * R ^ (-priceExponent j))
    (hroot : |(j : ℝ) * log Q - root| ≤ H * R ^ (-priceExponent j)),
    ∀ p : ℕ, p.Prime → Q - W * Q ^ bhpExponent ≤ (p : ℝ) →
      (p : ℝ) ≤ Q + W * Q ^ bhpExponent →
      |log (p : ℝ) - root / (j : ℝ)| ≤
        (2 * W + H) * R ^ (-priceExponent j) ∧
      |((V.readout ()) p j - beta 1 R) * log (p : ℝ)| ≤
        (2 * (A + 2 * W *
          (((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1) * (4 * (j : ℝ))))) *
          beta 1 R * log R * R ^ (-priceExponent j)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.pointwise_boundary_estimates

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.pointwise_boundary_estimates)) ↔ arena.Law actual := Iff.rfl

end pointwise_boundary_estimates

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeInventory
