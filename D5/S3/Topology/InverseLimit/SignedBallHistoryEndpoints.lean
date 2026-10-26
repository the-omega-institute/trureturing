/- GID: D5/S3/Topology/InverseLimit/SignedBallHistoryEndpoints
   generality: G
   mirror-B: none(waiver:private-internal-step)
   mirror-E: none(waiver:private-internal-step)
   anchors: []
   utility: none
   digest: Original whole-birth oscillation on actual generated successor carriers. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor
import D5.S3.Topology.InverseLimit.SignedOrdinalHistory

/-! One actual selected successor transports the original whole birth sequence
and its quantitative clopen to the next state of the same constructed run. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal

namespace D5.S3.Topology.InverseLimit.SignedBallHistoryEndpoints

open SignedOrdinalSuccessor

/-- The even and odd columns of one literal successor give infinitely many
high and zero evaluations of every whole sequence of original norm-one lifts. -/
private theorem quantitative_g_infinite
    {a : Ordinal.{0}} {H : SignedProperLimit.Prefix (Order.succ a)}
    {ha : ω ≤ a} {P : Predecessor H ha} {launch : Launch a}
    {Q : Prepared H ha P launch} {t : Treatment a}
    (R : Result H ha P launch Q t)
    (s : ℕ → SignedMeasure R.coordinates.carrier)
    (hmap : ∀ n, (s n).map (R.literalProjection t.row) = Q.measure t.row t.label n)
    (hmass : ∀ n, (s n).totalVariation univ = 1) :
    {n | (1 : ℝ) / 6 ≤ s n R.quantitativeClopen}.Infinite ∧
      {n | s n R.quantitativeClopen = 0}.Infinite := by
  have heven : Injective (fun m : ℕ => (R.column (2 * m)).n) :=
    R.k_mono.injective.comp (fun i j hij => by omega)
  have hodd : Injective (fun m : ℕ => (R.column (2 * m + 1)).n) :=
    R.k_mono.injective.comp (fun i j hij => by omega)
  constructor
  · apply (Set.infinite_range_of_injective heven).mono
    rintro _ ⟨m, rfl⟩
    exact ((R.quantitative_g (2 * m) (s _) (hmap _) (hmass _)).1 (by omega)).le
  · apply (Set.infinite_range_of_injective hodd).mono
    rintro _ ⟨m, rfl⟩
    exact (R.quantitative_g (2 * m + 1) (s _) (hmap _) (hmass _)).2 (by omega)

open SignedProperLimit SignedOrdinalHistoryState SignedOrdinalHistoryEvent
open SignedOrdinalHistorySuccessor SignedOrdinalHistory

set_option backward.isDefEq.respectTransparency false in
/-- An actual ordinary event supplies one clopen on its actual next run carrier.
Its literal old-row projection reads the whole original birth sequence, for
every original label and every norm-one signed lift on that generated carrier. -/
private theorem original_birth_oscillation
    (hCH : Cardinal.continuum.{0} = ℵ₁) (θ : Stage) (d base : Label) :
    ∃ (a : Stage) (hθ : θ < a), base < a.1 ∧ d.1 < ord a ∧
      ∃ G : Clopens (K (run hCH (nextStage a)).H),
        ∀ s : ℕ → SignedMeasure (K (run hCH (nextStage a)).H),
          (∀ n, HEq ((s n).map (projection (run hCH (nextStage a)).H
            (oldRow (hθ.trans (show a < nextStage a from Order.lt_succ (ord a)))
              (newRow (ord θ) θ.2)))) ((run hCH θ).birth.measure d n)) →
          (∀ n, (s n).totalVariation univ = 1) →
          {n | (1 : ℝ) / 6 ≤ s n G}.Infinite ∧ {n | s n G = 0}.Infinite := by
  classical
  obtain ⟨a, hb, hθ, hd, _, t, R, hselected, htrow, _, hwhole⟩ :=
    ordinary_cofinal hCH θ d base
  rcases t with ⟨r, label⟩
  have hr : r = oldRow hθ (newRow (ord θ) θ.2) := Subtype.ext htrow
  subst r
  let r₀ := oldRow hθ (newRow (ord θ) θ.2)
  let r₁ := oldRow
    (hθ.trans (show a < nextStage a from Order.lt_succ (ord a))) (newRow (ord θ) θ.2)
  have hnext : (run hCH (nextStage a)).H = R.coordinates.extended := by
    calc
      _ = (run hCH a).event.result.coordinates.extended :=
        congrArg State.H (successor_execution hCH a)
      _ = R.coordinates.extended :=
        congrArg (fun S : Selected (run hCH a).event.Q => S.result.coordinates.extended) hselected
  refine ⟨a, hθ, hb, hd, ?_⟩
  rw [hnext]
  change ∃ G : Clopens (K R.coordinates.extended),
    ∀ s : ℕ → SignedMeasure (K R.coordinates.extended),
      (∀ n, HEq ((s n).map
        (projection R.coordinates.extended r₁))
        ((run hCH θ).birth.measure d n)) →
      (∀ n, (s n).totalVariation univ = 1) →
      {n | (1 : ℝ) / 6 ≤ s n G}.Infinite ∧ {n | s n G = 0}.Infinite
  let E : K R.coordinates.extended ≃ₜ R.coordinates.carrier :=
    Homeomorph.setCongr R.coordinates.top_carrier
  let B : Base R.coordinates.extended r₁ ≃ₜ Base (run hCH a).H r₀ :=
    Homeomorph.setCongr (R.coordinates.old_carrier (rowIndex r₀))
  let G : Clopens (K R.coordinates.extended) :=
    ⟨E ⁻¹' (R.quantitativeClopen : Set _), R.quantitativeClopen.isClopen.preimage E.continuous⟩
  refine ⟨G, ?_⟩
  intro s hs hn
  let sigma : ℕ → SignedMeasure R.coordinates.carrier := fun n => (s n).map E
  have hp (x : K R.coordinates.extended) :
      R.literalProjection r₀ (E x) = B (projection R.coordinates.extended r₁ x) := by
    apply Subtype.ext
    exact (R.coordinates.restrict_inverse r₀.1 r₀.2.2 (E x)).symm
  have hm (n : ℕ) :
      (sigma n).map (R.literalProjection r₀) = (run hCH a).event.Q.measure r₀ label n := by
    have he : (sigma n).map (R.literalProjection r₀) =
        (s n).map (fun x => B (projection R.coordinates.extended r₁ x)) := by
      apply VectorMeasure.ext
      intro A hA
      calc
        (sigma n).map (R.literalProjection r₀) A =
            sigma n (R.literalProjection r₀ ⁻¹' A) :=
          VectorMeasure.map_apply _ (R.literalProjection r₀).continuous.measurable hA
        _ = s n (E ⁻¹' (R.literalProjection r₀ ⁻¹' A)) :=
          VectorMeasure.map_apply _ E.continuous.measurable
            ((R.literalProjection r₀).continuous.measurable hA)
        _ = s n ((fun x : K R.coordinates.extended =>
            B (projection R.coordinates.extended r₁ x)) ⁻¹' A) := by
          congr 1
          ext x
          exact Iff.of_eq (congrArg (fun y : Base (run hCH a).H r₀ => y ∈ A) (hp x))
        _ = (s n).map (fun x => B (projection R.coordinates.extended r₁ x)) A :=
          (VectorMeasure.map_apply (s n)
            (B.continuous.measurable.comp
              (projection R.coordinates.extended r₁).continuous.measurable) hA).symm
    have hcast : ∀ {C D : Set (Cube (ord θ))} (h : C = D)
        (p : K R.coordinates.extended → C),
        letI : MeasurableSpace C := borel C
        letI : MeasurableSpace D := borel D
        HEq ((s n).map (fun x => Homeomorph.setCongr h (p x))) ((s n).map p) := by
      intro C D h p
      subst D
      rfl
    exact eq_of_heq ((heq_of_eq he).trans
      ((hcast (R.coordinates.old_carrier (rowIndex r₀))
        (projection R.coordinates.extended r₁)).trans ((hs n).trans (hwhole n).symm)))
  have hnorm (n : ℕ) : (sigma n).totalVariation univ = 1 := by
    have hv : ((s n).map E).variation = (s n).variation.map E :=
      E.toMeasurableEquiv.measurableEmbedding.variation_map
    change SignedMeasure.totalVariation ((s n).map E) univ = 1
    rw [SignedMeasure.totalVariation_eq_variation, hv,
      Measure.map_apply E.continuous.measurable MeasurableSet.univ, preimage_univ,
      ← SignedMeasure.totalVariation_eq_variation, hn n]
  have heval (n : ℕ) : sigma n R.quantitativeClopen = s n G :=
    VectorMeasure.map_apply _ E.continuous.measurable R.quantitativeClopen.isClopen.1.measurableSet
  simpa only [heval] using quantitative_g_infinite R sigma hm hnorm

end D5.S3.Topology.InverseLimit.SignedBallHistoryEndpoints
