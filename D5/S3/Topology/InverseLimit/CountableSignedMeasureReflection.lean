/- GID: D5/S3/Topology/InverseLimit/CountableSignedMeasureReflection
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/CountableSignedMeasureReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One proper stage preserves every Jordan whole mass of a countable signed family. -/

import D5.S3.Topology.InverseLimit.CountableClopenReflection
import D5.S3.Topology.Measures.PositiveClopenMass
import D5.S3.Topology.Measures.RegularSignedLift
import D5.S3.Topology.Measures.NormPreservingLifts

/-!
# Simultaneous exact signed norm reflection

Countably many clopen near-maximizers force equality in variation contraction
at one proper stage. The equality persists at every later stage. Supplied
clopens descend at the same stage, with exact traces, nonemptiness,
disjointness and variation-nullity. No CH hypothesis or isometric projection
is assumed, and no final signed collision is supplied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Set Function MeasureTheory

namespace D5.S3.Topology.InverseLimit.CountableSignedMeasureReflection

open CountableClopenReflection

universe u v w

/-- Exact whole masses, in the original extended nonnegative real units. -/
def PreservesJordanMass {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] (s : SignedMeasure X) (p : X → Y) : Prop :=
  (SignedMeasure.totalVariation (s.map p)) univ = s.totalVariation univ ∧
  (SignedMeasure.toJordanDecomposition (s.map p)).posPart univ =
    s.toJordanDecomposition.posPart univ ∧
  (SignedMeasure.toJordanDecomposition (s.map p)).negPart univ =
    s.toJordanDecomposition.negPart univ

private lemma variation_real_eq {X : Type u} [MeasurableSpace X] (s : SignedMeasure X) :
    s.totalVariation.real univ = s.toJordanDecomposition.posPart.real univ +
      s.toJordanDecomposition.negPart.real univ := by
  exact measureReal_add_apply

private lemma positive_mass_map_le {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] (s : SignedMeasure X)
    (p : X → Y) (hp : Measurable p) :
    (SignedMeasure.toJordanDecomposition (s.map p)).posPart.real univ ≤
      s.toJordanDecomposition.posPart.real univ := by
  have htv : (SignedMeasure.totalVariation (s.map p)) univ ≤ s.totalVariation univ := by
    simpa only [← SignedMeasure.totalVariation_eq_variation,
      Measure.map_apply hp MeasurableSet.univ, preimage_univ] using
      (VectorMeasure.variation_map_le (μ := s) (φ := p) univ)
  have hr := ENNReal.toReal_mono (measure_ne_top s.totalVariation univ) htv
  have hm : (s.map p) univ = s univ := by
    rw [VectorMeasure.map_apply s hp MeasurableSet.univ, preimage_univ]
  have hs := s.apply_eq_posPart_real_sub_negPart_real MeasurableSet.univ
  have ht := SignedMeasure.apply_eq_posPart_real_sub_negPart_real (s.map p) MeasurableSet.univ
  have hv := variation_real_eq s
  have hw := variation_real_eq (s.map p)
  change (SignedMeasure.totalVariation (s.map p)).real univ ≤ s.totalVariation.real univ at hr
  linarith

private lemma preserves_of_positive_eq {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] (s : SignedMeasure X)
    (p : X → Y) (hp : Measurable p)
    (hpos : (SignedMeasure.toJordanDecomposition (s.map p)).posPart.real univ =
      s.toJordanDecomposition.posPart.real univ) : PreservesJordanMass s p := by
  have hm : (s.map p) univ = s univ := by
    rw [VectorMeasure.map_apply s hp MeasurableSet.univ, preimage_univ]
  have hs := s.apply_eq_posPart_real_sub_negPart_real MeasurableSet.univ
  have ht := SignedMeasure.apply_eq_posPart_real_sub_negPart_real (s.map p) MeasurableSet.univ
  have hn : (SignedMeasure.toJordanDecomposition (s.map p)).negPart.real univ =
      s.toJordanDecomposition.negPart.real univ := by linarith
  have hv : (SignedMeasure.totalVariation (s.map p)).real univ = s.totalVariation.real univ := by
    rw [variation_real_eq, variation_real_eq, hpos, hn]
  exact ⟨(measureReal_eq_measureReal_iff).mp hv,
    (measureReal_eq_measureReal_iff).mp hpos, (measureReal_eq_measureReal_iff).mp hn⟩

/-- One proper stage reflects the supplied clopens and preserves the entire
countable signed family's variation and both Jordan whole masses. Preservation
holds at every later proper stage, including the returned stage itself. -/
theorem exists_common_stage {ι : Type w} [Countable ι]
    (F : CountableStageᵒᵖ ⥤ Profinite.{1}) [∀ j, Nonempty (F.obj j)]
    [∀ j, MeasurableSpace (F.obj j)] [∀ j, BorelSpace (F.obj j)]
    (C : Cone F) [MeasurableSpace C.pt] [BorelSpace C.pt] (hC : IsLimit C)
    (hs : ∀ {i j} (f : i ⟶ j), Surjective (F.map f))
    (base : CountableStage) (s : ℕ → SignedMeasure C.pt)
    [∀ n, (s n).totalVariation.Regular]
    (W : ι → Set C.pt) (hW : ∀ i, IsClopen (W i)) :
    ∃ β : CountableStage, base ≤ β ∧
      ∃ V : ι → Set (F.obj (op β)),
        (∀ i, IsClopen (V i)) ∧
        (∀ i, W i = C.π.app (op β) ⁻¹' V i) ∧
        (∀ i, (V i).Nonempty ↔ (W i).Nonempty) ∧
        (∀ i j, Disjoint (V i) (V j) ↔ Disjoint (W i) (W j)) ∧
        (∀ γ : CountableStage, β ≤ γ → ∀ n,
          PreservesJordanMass (s n) (fun x : C.pt => C.π.app (op γ) x) ∧
          (SignedMeasure.totalVariation ((s n).map (fun x : C.pt => C.π.app (op γ) x))) =
            (s n).totalVariation.map (fun x : C.pt => C.π.app (op γ) x)) ∧
        (∀ n i, (SignedMeasure.totalVariation ((s n).map (fun x : C.pt => C.π.app (op β) x))) (V i)ᶜ = 0 ↔
          (s n).totalVariation (W i)ᶜ = 0) := by
  classical
  have happrox (n k : ℕ) : ∃ A : Set C.pt, IsClopen A ∧ A ⊆ univ ∧
      (s n).toJordanDecomposition.posPart.real univ - 1 / (k + 1 : ℝ) < (s n) A := by
    obtain ⟨hp, hn⟩ :=
      Measures.RegularSignedLift.regular_jordanParts_of_regular_totalVariation (s n)
    apply Measures.PositiveClopenMass.exists_isClopen_subset_lt_apply_of_lt_posPart
      (s n) hp hn isOpen_univ
    have he : 0 < 1 / (k + 1 : ℝ) := by positivity
    linarith
  choose A hA hAsub hAlower using happrox
  let T : (ℕ × ℕ) ⊕ ι → Set C.pt := Sum.elim (fun nk => A nk.1 nk.2) W
  have hT : ∀ i, IsClopen (T i) := by
    intro i
    cases i with
    | inl nk => exact hA nk.1 nk.2
    | inr i => exact hW i
  obtain ⟨β, hb, U, hU, hTU, hUne, hUdis⟩ :=
    CountableClopenReflection.exists_common_stage F C hC hs base T hT
  let p : C.pt → F.obj (op β) := C.π.app (op β)
  have hp : Measurable p :=
    (show Continuous p from (C.π.app (op β)).hom.hom.continuous).measurable
  have hpos (n : ℕ) : (SignedMeasure.toJordanDecomposition ((s n).map p)).posPart.real univ =
      (s n).toJordanDecomposition.posPart.real univ := by
    apply le_antisymm (positive_mass_map_le (s n) p hp)
    by_contra h
    have hgap : 0 < (s n).toJordanDecomposition.posPart.real univ -
        (SignedMeasure.toJordanDecomposition ((s n).map p)).posPart.real univ := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hgap
    have heval : (s n) (A n k) = ((s n).map p) (U (.inl (n, k))) := by
      rw [VectorMeasure.map_apply (s n) hp (hU _).isClosed.measurableSet]
      exact congrArg (s n) (hTU (.inl (n, k)))
    have hbound : (s n) (A n k) ≤
        (SignedMeasure.toJordanDecomposition ((s n).map p)).posPart.real univ := by
      rw [heval, SignedMeasure.apply_eq_posPart_real_sub_negPart_real ((s n).map p)
        (hU _).isClosed.measurableSet]
      have hmono := measureReal_mono (μ := (SignedMeasure.toJordanDecomposition ((s n).map p)).posPart)
        (subset_univ (U (.inl (n, k))))
      have hn : 0 ≤ (SignedMeasure.toJordanDecomposition ((s n).map p)).negPart.real
          (U (.inl (n, k))) := measureReal_nonneg
      linarith
    linarith [hAlower n k]
  have hall (γ : CountableStage) (hβγ : β ≤ γ) (n : ℕ) :
      PreservesJordanMass (s n) (fun x : C.pt => C.π.app (op γ) x) ∧
      (SignedMeasure.totalVariation ((s n).map (fun x : C.pt => C.π.app (op γ) x))) =
        (s n).totalVariation.map (fun x : C.pt => C.π.app (op γ) x) := by
    let q : C.pt → F.obj (op γ) := C.π.app (op γ)
    have hq : Measurable q :=
      (show Continuous q from (C.π.app (op γ)).hom.hom.continuous).measurable
    let f : op γ ⟶ op β := (homOfLE hβγ).op
    have hf : Measurable (F.map f) := (F.map f).hom.hom.continuous.measurable
    have hcomp : ((s n).map q).map (F.map f) = (s n).map p := by
      ext B hB
      rw [VectorMeasure.map_apply _ hf hB, VectorMeasure.map_apply _ hq (hf hB),
        VectorMeasure.map_apply _ hp hB]
      congr 1
      ext x
      have he := ConcreteCategory.congr_hom (C.w f) x
      change F.map f (q x) ∈ B ↔ p x ∈ B
      exact he ▸ Iff.rfl
    have hlow := positive_mass_map_le ((s n).map q) (F.map f) hf
    rw [hcomp, hpos n] at hlow
    have hposq := le_antisymm (positive_mass_map_le (s n) q hq) hlow
    have hm := preserves_of_positive_eq (s n) q hq hposq
    exact ⟨hm, Measures.NormPreservingLifts.totalVariation_map_of_mass (s n) q hq hm.1⟩
  refine ⟨β, hb, (fun i => U (.inr i)), (fun i => hU _),
    (fun i => hTU (.inr i)), (fun i => hUne (.inr i)),
    (fun i j => hUdis (.inr i) (.inr j)), hall, ?_⟩
  intro n i
  rw [(hall β le_rfl n).2]
  change ((s n).totalVariation.map p) (U (.inr i))ᶜ = 0 ↔ _
  rw [Measure.map_apply hp (hU (.inr i)).isClosed.measurableSet.compl,
    preimage_compl, ← hTU (.inr i)]
  rfl

end D5.S3.Topology.InverseLimit.CountableSignedMeasureReflection
