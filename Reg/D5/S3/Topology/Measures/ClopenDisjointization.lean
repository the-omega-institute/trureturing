import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.ClopenDisjointization

/-!
# Source-family attempt for clopen disjointization

The candidate relation keeps the complete nonmetric source telescope and
the actual index and clopen witnesses. The arenas and equivalence bridges
are a registration attempt, not a four-slot registration. Whole-family
variation, sensitivity, observational dependence and raw sourceSelection
remain absent. The source reconstruction boundary is the one tracked by
https://github.com/the-omega-institute/trureturing/issues/16293.
-/

namespace Reg.D5.S3.Topology.Measures.ClopenDisjointization

open Set MeasureTheory
open scoped Function
open _root_.D5.S3.Topology.Measures.ClopenDisjointization
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe u

structure SpaceData where
  K : Type u
  top : TopologicalSpace K
  compact : @CompactSpace K top
  hausdorff : @T2Space K top
  measurable : MeasurableSpace K
  borel : @BorelSpace K top measurable
  zeroDimensional : @ZeroDimensionalSpace K top

namespace Positive

structure Inputs where
  space : SpaceData.{u}
  measures : letI := space.measurable; ℕ → ProbabilityMeasure space.K
  regular : letI := space.top; letI := space.measurable
    ∀ n, (measures n : Measure space.K).Regular
  carriers : ℕ → Set space.K
  measurableCarriers : letI := space.measurable
    ∀ n, MeasurableSet (carriers n)
  disjointCarriers : Pairwise (Disjoint on carriers)
  carried : letI := space.measurable
    ∀ n, (measures n : Measure space.K) (carriers n) = 1
  tolerance : ℝ
  positiveTolerance : 0 < tolerance
  toleranceLtOne : tolerance < 1

abbrev Candidate (P : Inputs.{u}) := (ℕ → ℕ) × (ℕ → Set P.space.K)

def good (P : Inputs.{u}) (x : Candidate P) : Prop :=
  letI := P.space.top
  letI := P.space.measurable
  StrictMono x.1 ∧ Pairwise (Disjoint on x.2) ∧
    ∀ k, IsClopen (x.2 k) ∧ (x.2 k).Nonempty ∧
      1 - P.tolerance / 2 < (P.measures (x.1 k) : Measure P.space.K).real (x.2 k)

def signature : DependentFamily.Signature where
  Params := Inputs.{u}
  State := Candidate
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ P x => good P x) (fun a => nomatch a)

def arena : DependentFamily.Arena where
  signature := signature.{u}
  Law := fun R => ∀ P, ∃ x, R.readout () P x

abbrev sourceScope := type_of% (@exists_clopen_disjointization.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    letI := P.space.top
    letI := P.space.compact
    letI := P.space.hausdorff
    letI := P.space.measurable
    letI := P.space.borel
    letI := P.space.zeroDimensional
    obtain ⟨n, W, hgood⟩ := h P.measures P.regular P.carriers
      P.measurableCarriers P.disjointCarriers P.carried
      P.positiveTolerance P.toleranceLtOne
    exact ⟨⟨n, W⟩, hgood⟩
  · intro h K top compact hausdorff measurable borel zeroDimensional
      measures regular carriers measurableCarriers disjointCarriers carried tolerance
      positiveTolerance toleranceLtOne
    let P : Inputs.{u} :=
      ⟨⟨K, top, compact, hausdorff, measurable, borel, zeroDimensional⟩,
        measures, regular, carriers, measurableCarriers, disjointCarriers, carried,
        tolerance, positiveTolerance, toleranceLtOne⟩
    obtain ⟨x, hx⟩ := h P
    exact ⟨x.1, x.2, hx⟩

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@exists_clopen_disjointization.{u})

end Positive

namespace Signed

structure Inputs where
  space : SpaceData.{u}
  measures : letI := space.measurable; ℕ → SignedMeasure space.K
  regular : letI := space.top; letI := space.measurable
    ∀ n, (measures n).totalVariation.Regular
  normOne : letI := space.measurable
    ∀ n, (measures n).totalVariation.real univ = 1
  carriers : ℕ → Set space.K
  measurableCarriers : letI := space.measurable
    ∀ n, MeasurableSet (carriers n)
  disjointCarriers : Pairwise (Disjoint on carriers)
  carried : letI := space.measurable
    ∀ n, (measures n).totalVariation (carriers n)ᶜ = 0
  tolerance : ℝ
  positiveTolerance : 0 < tolerance
  toleranceLtOne : tolerance < 1

abbrev Candidate (P : Inputs.{u}) :=
  letI := P.space.measurable
  (ℕ → ℕ) × (ℕ → Set P.space.K) × (ℕ → SignedMeasure P.space.K)

def good (P : Inputs.{u}) (x : Candidate P) : Prop :=
  letI := P.space.top
  letI := P.space.measurable
  let n := x.1
  let W := x.2.1
  let t := x.2.2
  let v := P.measures
  let η := P.tolerance
  StrictMono n ∧ Pairwise (Disjoint on W) ∧
    (∀ k, let q := (v (n k)).totalVariation.real (W k)
      IsClopen (W k) ∧ (W k).Nonempty ∧ 1 - η < q ∧ 0 < q ∧ q ≤ 1 ∧
        t k = q⁻¹ • (v (n k)).restrict (W k) ∧
        (t k).totalVariation.Regular ∧ (t k).totalVariation.real univ = 1 ∧
        (t k).totalVariation (W k)ᶜ = 0 ∧
        (t k - v (n k)).totalVariation.real univ = 2 * (1 - q) ∧
        (t k - v (n k)).totalVariation.real univ < 2 * η) ∧
    ∃ s : ℝ, ∃ j : ℕ → ℕ, (s = 1 ∨ s = -1) ∧ StrictMono j ∧
      StrictMono (n ∘ j) ∧
      ∀ k, (s • t (j k)).totalVariation = (t (j k)).totalVariation ∧
        (s • v (n (j k))).totalVariation = (v (n (j k))).totalVariation ∧
        (1 / 2 : ℝ) ≤ (s • t (j k)).toJordanDecomposition.posPart.real univ ∧
        (s • t (j k) - s • v (n (j k))).totalVariation.real univ =
          2 * (1 - (v (n (j k))).totalVariation.real (W (j k)))

def signature : DependentFamily.Signature where
  Params := Inputs.{u}
  State := Candidate
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ P x => good P x) (fun a => nomatch a)

def arena : DependentFamily.Arena where
  signature := signature.{u}
  Law := fun R => ∀ P, ∃ x, R.readout () P x

abbrev sourceScope := type_of% (@exists_signed_clopen_disjointization.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    letI := P.space.top
    letI := P.space.compact
    letI := P.space.hausdorff
    letI := P.space.measurable
    letI := P.space.borel
    letI := P.space.zeroDimensional
    obtain ⟨n, W, t, hgood⟩ := h P.measures P.regular P.normOne P.carriers
      P.measurableCarriers P.disjointCarriers P.carried
      P.positiveTolerance P.toleranceLtOne
    exact ⟨⟨n, W, t⟩, hgood⟩
  · intro h K top compact hausdorff measurable borel zeroDimensional
      measures regular normOne carriers measurableCarriers disjointCarriers carried tolerance
      positiveTolerance toleranceLtOne
    let P : Inputs.{u} :=
      ⟨⟨K, top, compact, hausdorff, measurable, borel, zeroDimensional⟩,
        measures, regular, normOne, carriers, measurableCarriers, disjointCarriers, carried,
        tolerance, positiveTolerance, toleranceLtOne⟩
    obtain ⟨x, hx⟩ := h P
    exact ⟨x.1, x.2.1, x.2.2, hx⟩

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@exists_signed_clopen_disjointization.{u})

end Signed

end Reg.D5.S3.Topology.Measures.ClopenDisjointization
