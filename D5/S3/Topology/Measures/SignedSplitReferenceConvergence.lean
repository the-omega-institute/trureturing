/- GID: D5/S3/Topology/Measures/SignedSplitReferenceConvergence
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/SignedSplitReferenceConvergence
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Moving signed reference estimates on an actual closed Boolean split give represented whole-sequence weak-star convergence. -/

import D5.S3.Topology.Measures.ClopenCauchyConvergence
import Mathlib.Topology.InductiveDimension.Classes
import Mathlib.Topology.Metrizable.Uniformity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace D5.S3.Topology.Measures.SignedSplitReferenceConvergence

universe u

variable {K : Type u} [MetricSpace K] [CompactSpace K]
  [TotallyDisconnectedSpace K] [MeasurableSpace K] [BorelSpace K]

/-- The actual two closed sheets, with no coverage or nonemptiness premise. -/
def Split (Y Z : Set K) (_hY : IsClosed Y) (_hZ : IsClosed Z) :=
  {p : K × Bool // (p.1 ∈ Y ∧ p.2 = false) ∨ (p.1 ∈ Z ∧ p.2 = true)}

variable {Y Z : Set K} {hY : IsClosed Y} {hZ : IsClosed Z}

instance : TopologicalSpace (Split Y Z hY hZ) := by unfold Split; infer_instance
instance : MeasurableSpace (Split Y Z hY hZ) := by unfold Split; infer_instance
instance : BorelSpace (Split Y Z hY hZ) := by unfold Split; infer_instance
instance : T2Space (Split Y Z hY hZ) := by unfold Split; infer_instance
instance : TopologicalSpace.MetrizableSpace (Split Y Z hY hZ) := by
  letI : TopologicalSpace.MetrizableSpace K := inferInstance
  letI : TopologicalSpace.MetrizableSpace Bool := inferInstance
  letI : TopologicalSpace.MetrizableSpace (K × Bool) :=
    TopologicalSpace.metrizableSpace_prod
  exact TopologicalSpace.MetrizableSpace.subtype _
instance : TotallyDisconnectedSpace (Split Y Z hY hZ) := by unfold Split; infer_instance

instance : CompactSpace (Split Y Z hY hZ) := by
  change CompactSpace {p : K × Bool //
    (p.1 ∈ Y ∧ p.2 = false) ∨ (p.1 ∈ Z ∧ p.2 = true)}
  apply isCompact_iff_compactSpace.mp
  exact (((hY.preimage continuous_fst).inter
    (isClosed_singleton.preimage continuous_snd)).union
    ((hZ.preimage continuous_fst).inter
    (isClosed_singleton.preimage continuous_snd))).isCompact

/-- The actual first-coordinate projection. -/
def projection (x : Split Y Z hY hZ) : K := x.val.1

/-- A closed and open Boolean sheet of the split. -/
def side (e : Bool) : Set (Split Y Z hY hZ) := {x | x.val.2 = e}

private lemma continuous_projection : Continuous (projection (hY := hY) (hZ := hZ)) :=
  continuous_fst.comp continuous_subtype_val

private lemma clopen_side (e : Bool) : IsClopen (side (hY := hY) (hZ := hZ) e) :=
  (isClopen_discrete ({e} : Set Bool)).preimage
    (continuous_snd.comp continuous_subtype_val)

private lemma projection_injective_on_side (e : Bool) :
    Set.InjOn (projection (hY := hY) (hZ := hZ)) (side e) := by
  intro x hx y hy hxy
  apply Subtype.ext
  exact Prod.ext hxy (hx.trans hy.symm)

/-- Each relative clopen trace on a fixed sheet extends to an ambient clopen.
The projected compact traces themselves need not be ambient clopens. -/
private lemma exists_clopen_trace (W : Set (Split Y Z hY hZ))
    (hW : IsClopen W) (e : Bool) :
    ∃ B : Set K, IsClopen B ∧
      W ∩ side e = side e ∩ projection ⁻¹' B := by
  let P : Set K := projection '' (W ∩ side e)
  let Q : Set K := projection '' (Wᶜ ∩ side e)
  have hP : IsClosed P :=
    ((hW.isClosed.inter (clopen_side e).isClosed).isCompact.image
      continuous_projection).isClosed
  have hQ : IsClosed Q :=
    ((hW.compl.isClosed.inter (clopen_side e).isClosed).isCompact.image
      continuous_projection).isClosed
  have hPQ : P ⊆ Qᶜ := by
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have : y = x := projection_injective_on_side e hy.2 hx.2 hxy
    exact hy.1 (this.symm ▸ hx.1)
  obtain ⟨B, hB, hPB, hBQ⟩ := exists_clopen_of_closed_subset_open hP hQ.isOpen_compl hPQ
  refine ⟨B, hB, ?_⟩
  ext x
  constructor
  · intro hx
    exact ⟨hx.2, hPB ⟨x, hx, rfl⟩⟩
  · rintro ⟨hxside, hxB⟩
    refine ⟨?_, hxside⟩
    by_contra hxW
    exact hBQ hxB ⟨x, ⟨hxW, hxside⟩, rfl⟩

private lemma side_partition (A : Set K) :
    projection ⁻¹' A =
      (side false ∩ projection ⁻¹' A) ∪
      (side true ∩ projection (hY := hY) (hZ := hZ) ⁻¹' A) := by
  ext x
  cases h : x.val.2 <;> simp [side, h]

private lemma disjoint_sides (A B : Set K) :
    Disjoint (side false ∩ projection ⁻¹' A)
      (side true ∩ projection (hY := hY) (hZ := hZ) ⁻¹' B) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact Bool.false_ne_true (hx.1.symm.trans hy.1)

private lemma signed_three_term (r : SignedMeasure (Split Y Z hY hZ))
    (W : Set (Split Y Z hY hZ)) (B₀ B₁ : Set K)
    (hB₀ : IsClopen B₀) (hB₁ : IsClopen B₁)
    (h₀ : W ∩ side false = side false ∩ projection ⁻¹' B₀)
    (h₁ : W ∩ side true = side true ∩ projection ⁻¹' B₁) :
    r W = (r.map projection) B₀ - r (side true ∩ projection ⁻¹' B₀) +
      r (side true ∩ projection ⁻¹' B₁) := by
  have hm (e : Bool) (B : Set K) (hB : IsClopen B) :
      MeasurableSet (side e ∩ projection (hY := hY) (hZ := hZ) ⁻¹' B) :=
    ((clopen_side e).inter (hB.preimage continuous_projection)).isClosed.measurableSet
  have hW : W = (side false ∩ projection ⁻¹' B₀) ∪
      (side true ∩ projection ⁻¹' B₁) := by
    rw [← h₀, ← h₁]
    ext x
    cases h : x.val.2 <;> simp [side, h]
  have hproj : (r.map projection) B₀ =
      r (side false ∩ projection ⁻¹' B₀) + r (side true ∩ projection ⁻¹' B₀) := by
    rw [VectorMeasure.map_apply r continuous_projection.measurable hB₀.isClosed.measurableSet]
    calc
      r (projection ⁻¹' B₀) =
          r ((side false ∩ projection ⁻¹' B₀) ∪ (side true ∩ projection ⁻¹' B₀)) :=
        congrArg r (side_partition B₀)
      _ = _ := VectorMeasure.of_union (disjoint_sides B₀ B₀)
        (hm false B₀ hB₀) (hm true B₀ hB₀)
  rw [hW, VectorMeasure.of_union (disjoint_sides B₀ B₁)
    (hm false B₀ hB₀) (hm true B₁ hB₁), hproj]
  ring

/-- A fixed signed reference measure and a moving increasing-set side estimate
control all new clopen coordinates, hence the whole represented signed sequence. -/
theorem exists_signed_limit_of_reference
    (Y Z : Set K) (hY : IsClosed Y) (hZ : IsClosed Z)
    (C : ℝ) (hC : 0 ≤ C) (s : ℕ → SignedMeasure (Split Y Z hY hZ))
    (hbound : ∀ n, (s n).totalVariation.real univ ≤ C)
    (μ : SignedMeasure K) (U : ℕ → Set K)
    (hU : ∀ n, MeasurableSet (U n)) (hmono : Monotone U)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hproj : ∀ A : Set K, IsClopen A →
      Tendsto (fun n => ((s n).map projection) A) atTop (𝓝 (μ A)))
    (hside : ∀ A : Set K, IsClopen A → ∀ᶠ n in atTop,
      |(s n) (side true ∩ projection ⁻¹' A) - μ (A ∩ U n)| ≤ ε n) :
    ∃ ν : SignedMeasure (Split Y Z hY hZ),
      ν.totalVariation.real univ ≤ C ∧
      Measure.Regular ν.toJordanDecomposition.posPart ∧
      Measure.Regular ν.toJordanDecomposition.negPart ∧
      Tendsto (fun n => (NormPreservingLifts.signedFunctional (s n)).toWeakDual)
        atTop (𝓝 (NormPreservingLifts.signedFunctional ν).toWeakDual) := by
  letI : MetricSpace (Split Y Z hY hZ) := TopologicalSpace.metrizableSpaceMetric _
  have htrue (A : Set K) (hA : IsClopen A) :
      Tendsto (fun n => (s n) (side true ∩ projection ⁻¹' A)) atTop
        (𝓝 (μ (A ∩ ⋃ n, U n))) := by
    have hmoving : Tendsto (fun n => μ (A ∩ U n)) atTop
        (𝓝 (μ (A ∩ ⋃ n, U n))) := by
      simpa only [Set.inter_iUnion] using
        μ.tendsto_vectorMeasure_iUnion_atTop_nat
          (fun i j hij => Set.inter_subset_inter_right A (hmono hij))
          (fun n => hA.isClosed.measurableSet.inter (hU n))
    have herr : Tendsto (fun n =>
        (s n) (side true ∩ projection ⁻¹' A) - μ (A ∩ U n)) atTop (𝓝 0) := by
      exact squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hside A hA) hε
    have h := herr.add hmoving
    simpa only [zero_add, sub_add_cancel] using h
  apply ClopenCauchyConvergence.tendsto_signedFunctional_of_clopen_cauchy C hC s hbound
  intro W hW
  obtain ⟨B₀, hB₀, h₀⟩ := exists_clopen_trace W hW false
  obtain ⟨B₁, hB₁, h₁⟩ := exists_clopen_trace W hW true
  have h := ((hproj B₀ hB₀).sub (htrue B₀ hB₀)).add (htrue B₁ hB₁)
  have hw : Tendsto (fun n => (s n) W) atTop
      (𝓝 (μ B₀ - μ (B₀ ∩ ⋃ n, U n) + μ (B₁ ∩ ⋃ n, U n))) := by
    convert h using 1
    ext n
    exact signed_three_term (s n) W B₀ B₁ hB₀ hB₁ h₀ h₁
  exact hw.cauchySeq

end D5.S3.Topology.Measures.SignedSplitReferenceConvergence
