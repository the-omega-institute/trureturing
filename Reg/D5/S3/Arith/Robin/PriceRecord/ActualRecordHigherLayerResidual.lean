import D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- Faithful source-type mirror proposals, UNCOMPILED_UNACCEPTED.
Each arena retains the complete source telescope and changes only the stated
readout in its conclusion. No Contract.Registration, binding certificate or
four-slot acceptance is fabricated. Variation, sensitivity, observational
dependence, exact sourceSelection and producer binding remain open.
The existing incomplete owner registration is unchanged. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual

open Real Finset
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.Robin.EulerLayerRootCorrection (strict_inventory_third_layer_mass)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity (layerPrime)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace finite_complete_higher_layer_bound

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
  realize signature (fun _ X m => completeHigherLayerLoss X m) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {X R : ℝ} {m : ℕ} {mu : ℝ}
    (hX : 1 < X) (hm : 2 ≤ m) (hmu : 0 < mu)
    (hrecord : ∀ k : ℕ, 0 < k → k < m →
      goldenResourceObjective mu k < goldenResourceObjective mu m)
    (hR : 1 ≤ R) (hRP : R < (largestPrime m : ℝ))
    (hclock : X * log X ≤ log 2 * R ^ 3),
    0 ≤ V.readout () X m ∧
    V.readout () X m ≤
      2 * (⌊R⌋₊ : ℝ) / (largestPrime m : ℝ) +
        referencePrice X * strict_inventory_third_layer_mass m ∧
    V.readout () X m ≤
      2 * R / (largestPrime m : ℝ) + referencePrice X *
        ((layerPrime m 3 : ℝ) * log (4 * (largestPrime m : ℝ) ^ 2))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.finite_complete_higher_layer_bound

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.finite_complete_higher_layer_bound)) ↔ arena.Law actual := Iff.rfl

end finite_complete_higher_layer_bound

namespace compact_second_raw_margin

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
  realize signature (fun _ X t => secondRawMargin X t) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {X K s : ℝ} (hX : 1 < X) (hK : 0 ≤ K)
    (hs : |s| ≤ K) (hlarge : 2 * K ≤ sqrt 2 * log X)
    (ht : 1 < secondTubePoint X s),
    |X * log X * V.readout () X (secondTubePoint X s) +
      s / sqrt 2 + log (sqrt 2)| ≤ secondExpansionError X K

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.compact_second_raw_margin

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.compact_second_raw_margin)) ↔ arena.Law actual := Iff.rfl

end compact_second_raw_margin

namespace finite_actual_second_layer_tube_bound

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
  realize signature (fun _ X n => actualDefect X n - completeFirstLayerLoss X n - completeHigherLayerLoss X n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {X δ : ℝ} {n : ℕ}
    (hX : 1 < X) (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hanti : ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      n.factorization q ≤ n.factorization p)
    (hlarge : 2 * (|secondTubeCenter| + 1) ≤ sqrt 2 * log X)
    (hrem : secondExpansionError X (|secondTubeCenter| + 1) ≤ δ / (2 * sqrt 2))
    (hA : sqrt X < secondTubePoint X (secondTubeCenter - δ))
    (hQlo : secondTubePoint X (secondTubeCenter - δ) < (layerPrime n 2 : ℝ))
    (hQhi : (layerPrime n 2 : ℝ) < secondTubePoint X (secondTubeCenter + δ))
    (hθlo : |Chebyshev.theta (secondTubePoint X (secondTubeCenter - δ)) -
      secondTubePoint X (secondTubeCenter - δ)| ≤ δ * sqrt X / (2 * log X))
    (hθhi : |Chebyshev.theta (secondTubePoint X (secondTubeCenter + δ)) -
      secondTubePoint X (secondTubeCenter + δ)| ≤ δ * sqrt X / (2 * log X)),
    0 ≤ sqrt X * log X ^ 3 *
      (V.readout () X n) ∧
    sqrt X * log X ^ 3 *
      (V.readout () X n) ≤
        9 * δ ^ 2 / sqrt 2

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.finite_actual_second_layer_tube_bound

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual.finite_actual_second_layer_tube_bound)) ↔ arena.Law actual := Iff.rfl

end finite_actual_second_layer_tube_bound

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
