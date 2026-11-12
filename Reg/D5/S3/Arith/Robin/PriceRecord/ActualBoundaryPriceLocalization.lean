import D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- Full-telescope actual laws and definitional source bridges.
Four-slot registration is unfinished: no lawful enrolled-template application,
compiler occurrence/sourceSelection binding, whole-family intervention,
fixed-coordinate sensitivity or observational-dependence proof is asserted.
The shared DependentFamily enrollment alone supplies none of those client proofs. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
open Real Filter Finset
open scoped Topology BigOperators
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace price_variation
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
  realize signature (fun _ p x => beta p x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {j : ℕ} (hj : 1 ≤ j) {a x y : ℝ}
    (ha : 2 ≤ a) (hx : a ≤ x) (hy : a ≤ y),
    |(V.readout ()) j y - (V.readout ()) j x| ≤ priceLip j a * |y - x|

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.price_variation

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.price_variation)) ↔ arena.Law actual := Iff.rfl

end price_variation

namespace uniform_coarse_geometry
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
  Law V := ∀ (j : ℕ) (hj : 2 ≤ j),
    ∃ T : ℝ, 0 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      FullRecord m mu → T ≤ (largestPrime m : ℝ) →
      4 ≤ (largestPrime m : ℝ) ∧ 4 ≤ ((V.readout ()) m j : ℝ) ∧
      ((V.readout ()) m j : ℝ) ≤ (largestPrime m : ℝ) / 8 ∧
      ((V.readout ()) m 2 : ℝ) < (largestPrime m : ℝ) / 2 ∧
      log (largestPrime m : ℝ) / (4 * (j : ℝ)) ≤ log (((V.readout ()) m j : ℝ) / 2)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.uniform_coarse_geometry

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.uniform_coarse_geometry)) ↔ arena.Law actual := Iff.rfl

end uniform_coarse_geometry

namespace counted_higher_pools
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => primesIn p x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {N K : ℕ} {C c X : ℝ}
    (hcount : ∀ x : ℝ, X ≤ x →
      c * x ^ bhpExponent / log x ≤ (((V.readout ()) (x - C * x ^ bhpExponent) x).card : ℝ) ∧
      c * x ^ bhpExponent / log x ≤ (((V.readout ()) x (x + C * x ^ bhpExponent)).card : ℝ))
    (hXN : X ≤ (N : ℝ))
    (hcapacity : (K : ℝ) + 1 ≤ c * (N : ℝ) ^ bhpExponent / log N),
    ∃ Lo Hi : Finset ℕ, Lo.card = K ∧ Hi.card = K ∧
      (∀ p ∈ Lo, p.Prime ∧ (N : ℝ) - C * (N : ℝ) ^ bhpExponent ≤ p ∧ (p : ℝ) ≤ N) ∧
      (∀ p ∈ Hi, p.Prime ∧ (N : ℝ) < p ∧ (p : ℝ) ≤ (N : ℝ) + C * (N : ℝ) ^ bhpExponent)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.counted_higher_pools

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.counted_higher_pools)) ↔ arena.Law actual := Iff.rfl

end counted_higher_pools

namespace uniform_counted_first_pools
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => primesIn p x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (j : ℕ) (hj : 2 ≤ j)
    (C c X : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hcount : ∀ x : ℝ, X ≤ x →
      c * x ^ bhpExponent / log x ≤
        (((V.readout ()) (x - C * x ^ bhpExponent) x).card : ℝ) ∧
      c * x ^ bhpExponent / log x ≤
        (((V.readout ()) x (x + C * x ^ bhpExponent)).card : ℝ)),
    ∃ T : ℝ, 0 < T ∧ ∀ P : ℕ, T ≤ (P : ℝ) →
      4 ≤ (P : ℝ) ∧
      0 ≤ C * (P : ℝ) ^ bhpExponent ∧
      C * (P : ℝ) ^ bhpExponent ≤ (P : ℝ) / 2 ∧
      ∃ FirstLo FirstHi : Finset ℕ,
        FirstLo.card = comparisonCount j P ∧ FirstHi.card = comparisonCount j P ∧
        (∀ p ∈ FirstLo, p.Prime ∧
          (P : ℝ) - C * (P : ℝ) ^ bhpExponent ≤ (p : ℝ) ∧ (p : ℝ) ≤ P) ∧
        (∀ p ∈ FirstHi, p.Prime ∧
          (P : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (P : ℝ) + C * (P : ℝ) ^ bhpExponent)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.uniform_counted_first_pools

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.uniform_counted_first_pools)) ↔ arena.Law actual := Iff.rfl

end uniform_counted_first_pools

namespace uniform_higher_geometry
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
  Law V := ∀ (j : ℕ) (hj : 2 ≤ j)
    (C c X : ℝ) (hC : 0 < C) (hc : 0 < c),
    ∃ T : ℝ, 0 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      FullRecord m mu → T ≤ (largestPrime m : ℝ) →
      let P : ℝ := largestPrime m
      let Q : ℝ := (V.readout ()) m j
      let K : ℕ := comparisonCount j P
      let w : ℝ := C * Q ^ bhpExponent
      X ≤ Q ∧ (K : ℝ) + 1 ≤ c * Q ^ bhpExponent / log Q ∧
        w ≤ Q / 2 ∧ ((V.readout ()) m (j + 1) : ℝ) < Q - w ∧
        Q + w ≤ ((V.readout ()) m (j - 1) : ℝ) ∧ P ≤ Q ^ j

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.uniform_higher_geometry

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.uniform_higher_geometry)) ↔ arena.Law actual := Iff.rfl

end uniform_higher_geometry

namespace first_beta_lower
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
  realize signature (fun _ p x => beta p x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {P : ℝ} (hP : 2 ≤ P),
    1 / (P * log P) ≤ 2 * (V.readout ()) 1 P

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.first_beta_lower

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.first_beta_lower)) ↔ arena.Law actual := Iff.rfl

end first_beta_lower

namespace priceLip_half_bound
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
  realize signature (fun _ p x => priceLip p x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (j : ℕ) {P Q D : ℝ}
    (hP : 1 < P) (hQ : 4 ≤ Q) (hD : 0 < D)
    (hlog : log P / D ≤ log (Q / 2)),
    (V.readout ()) j (Q / 2) ≤
      (((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1) * D) / (Q ^ (j + 1) * log P)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.priceLip_half_bound

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.priceLip_half_bound)) ↔ arena.Law actual := Iff.rfl

end priceLip_half_bound

namespace bhp_boundary_price_localization
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
  realize signature (fun _ p x => beta p x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := BHPMaximumGap → BHPShortIntervalCount →
    ∀ j : ℕ, 2 ≤ j → ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
    ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
      T ≤ (largestPrime m : ℝ) →
      |(V.readout ()) j (layerPrime m j : ℝ) - (V.readout ()) 1 (largestPrime m : ℝ)| ≤
        C * (V.readout ()) 1 (largestPrime m : ℝ) *
          (largestPrime m : ℝ) ^ (-priceExponent j)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.bhp_boundary_price_localization

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.bhp_boundary_price_localization)) ↔ arena.Law actual := Iff.rfl

end bhp_boundary_price_localization

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
