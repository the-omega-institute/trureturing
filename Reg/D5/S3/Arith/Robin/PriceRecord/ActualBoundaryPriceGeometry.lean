import D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceGeometry
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- Full-telescope actual laws and definitional source bridges.
Four-slot registration is unfinished: lawful enrolled-template application,
compiler occurrence/sourceSelection binding, whole-family intervention,
fixed-coordinate sensitivity and observational dependence remain unproved. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceGeometry
open Real Filter Finset
open scoped Topology BigOperators
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace priceLip_nonneg
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
  Law V := ∀ (j : ℕ) {a : ℝ} (ha : 2 ≤ a),
    0 ≤ (V.readout ()) j a

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.priceLip_nonneg

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.priceLip_nonneg)) ↔ arena.Law actual := Iff.rfl

end priceLip_nonneg

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

namespace actual_boundary_price_from_pools
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
  Law V := ∀ (j : ℕ) (hj : 2 ≤ j),
    ∃ T : ℝ, 0 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      FullRecord m mu → T ≤ (largestPrime m : ℝ) →
      let P : ℝ := largestPrime m
      let Q : ℝ := layerPrime m j
      let K : ℕ := comparisonCount j P
      ∀ w v : ℝ, 0 ≤ w → w ≤ Q / 2 → 0 ≤ v → v ≤ P / 2 →
      ∀ Lo Hi FirstLo FirstHi : Finset ℕ,
      Lo.card = K → Hi.card = K → FirstLo.card = K → FirstHi.card = K →
      (∀ p ∈ Lo, p.Prime ∧ Q - w ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧
        layerPrime m (j + 1) < p) →
      (∀ p ∈ Hi, p.Prime ∧ Q < (p : ℝ) ∧ (p : ℝ) ≤ Q + w ∧
        p ≤ layerPrime m (j - 1)) →
      (∀ p ∈ FirstLo, p.Prime ∧ P - v ≤ (p : ℝ) ∧ (p : ℝ) ≤ P) →
      (∀ p ∈ FirstHi, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ P + v) →
      |(V.readout ()) j Q - (V.readout ()) 1 P| ≤
        priceLip j (Q / 2) * w + priceLip 1 (P / 2) * v +
          (8 * (j : ℝ) / (K : ℝ)) * ((V.readout ()) 1 P + priceLip 1 (P / 2) * v)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.actual_boundary_price_from_pools

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization.actual_boundary_price_from_pools)) ↔ arena.Law actual := Iff.rfl

end actual_boundary_price_from_pools

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


universe u

namespace subset_just_above
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {α : Type u} [DecidableEq α] (S : Finset α)
    (f : α → ℝ) {t H : ℝ} (_ht : 0 ≤ t) (_hH : ∀ a ∈ S, (V.readout ()) () (f a) ≤ H)
    (_htotal : t < ∑ a ∈ S, (V.readout ()) () (f a)),
    ∃ D ⊆ S, t < ∑ a ∈ D, (V.readout ()) () (f a) ∧ (∑ a ∈ D, (V.readout ()) () (f a)) ≤ t + H

private theorem actual_law : (arena.{u}).Law actual := by
  exact @subset_just_above.{u}

private theorem source_bridge :
    (type_of% (@subset_just_above.{u})) ↔
      (arena.{u}).Law actual := Iff.rfl

private theorem actual_observational_dependence :
    ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

end subset_just_above

namespace subset_just_below
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {α : Type u} [DecidableEq α] (S : Finset α)
    (f : α → ℝ) {t H : ℝ} (_ht : 0 < t) (_hH : ∀ a ∈ S, (V.readout ()) () (f a) ≤ H)
    (_htotal : t ≤ ∑ a ∈ S, (V.readout ()) () (f a)),
    ∃ U ⊆ S, (∑ a ∈ U, (V.readout ()) () (f a)) < t ∧ t ≤ (∑ a ∈ U, (V.readout ()) () (f a)) + H

private theorem actual_law : (arena.{u}).Law actual := by
  exact @subset_just_below.{u}

private theorem source_bridge :
    (type_of% (@subset_just_below.{u})) ↔
      (arena.{u}).Law actual := Iff.rfl

private theorem actual_observational_dependence :
    ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

end subset_just_below

namespace exchange_mass_bound
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p a => goldenLayerMarginal p a) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {m : ℕ} {mu lambda h : ℝ}
    (_hm : 0 < m) (_hrecord : FullRecord m mu)
    (D U : Finset ℕ) (_hD : ∀ p ∈ D, p.Prime) (_hU : ∀ p ∈ U, p.Prime)
    (_hDvd : ∀ p ∈ D, p ∣ m) (_hdis : Disjoint D U)
    (_hbalance : logMass U < logMass D)
    (_hupper : (∑ p ∈ D, (V.readout ()) p (m.factorization p) * log p) ≤
      lambda * logMass D)
    (_hlower : h * logMass U ≤
      ∑ p ∈ U, (V.readout ()) p (m.factorization p + 1) * log p),
    h * logMass U < lambda * logMass D - mu * (logMass D - logMass U)

private theorem actual_law : arena.Law actual := by
  exact @exchange_mass_bound

private theorem source_bridge :
    (type_of% (@exchange_mass_bound)) ↔
      arena.Law actual := Iff.rfl

private theorem actual_observational_dependence :
    ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 1, 2, ?_⟩
  exact ne_of_gt (golden_layer_strict_decrease Nat.prime_two (by norm_num : 1 ≤ 1)
    (by norm_num : 1 < 2))

end exchange_mass_bound

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceGeometry
