/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalActualG
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalActualG
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Fixed quantitative clopen oscillation for all signed lifts on actual successors. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalActualReindex

/-! The same selected event controls all lifts on the literal successor space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalActualG

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open SignedOrdinalHistoryState SignedOrdinalRealization SignedOrdinalRealizationEvents
open SignedOrdinalActualReindex

variable (hCH : Cardinal.continuum.{0} = ℵ₁)

/-- The original selected quantitative clopen on the actual successor carrier. -/
noncomputable def clopen (a : Stage) :
    Clopens ((finalPrefix hCH).Space (nextStage a).1) :=
  ⟨successorHomeomorph hCH a ⁻¹'
      ((SignedOrdinalHistory.run hCH a).event.result.quantitativeClopen : Set _),
    (SignedOrdinalHistory.run hCH a).event.result.quantitativeClopen.isClopen.preimage
      (successorHomeomorph hCH a).continuous⟩

/-- These columns are fixed before any lift sequence is given. -/
noncomputable def column (a : Stage) (q : ℕ) : ℕ :=
  ((SignedOrdinalHistory.run hCH a).event.result.column q).n

theorem column_strictMono (a : Stage) : StrictMono (column hCH a) :=
  (SignedOrdinalHistory.run hCH a).event.result.k_mono

private theorem local_projection (a : Stage) (r : Rows (ord a))
    (x : (finalPrefix hCH).Space (nextStage a).1) :
    (SignedOrdinalHistory.run hCH a).event.result.literalProjection r
      (successorHomeomorph hCH a x) =
    Homeomorph.setCongr (carrier_read hCH a (rowIndex r))
      ((finalPrefix hCH).map ⟨r.1, r.2.2.trans_lt a.1.2⟩ (nextStage a).1
        (r.2.2.trans (Order.le_succ (ord a))) x) := by
  obtain ⟨y, rfl⟩ := (finalPrefix hCH).projection_surjective
    (Cardinal.isSuccLimit_omega 1) (nextStage a).1 x
  have hf := congrArg (fun p => p y) (projection_factor hCH
    ⟨r.1, r.2.2.trans_lt a.1.2⟩ (nextStage a).1
    (r.2.2.trans (Order.le_succ (ord a))))
  change (finalPrefix hCH).map _ _ _ ((finalPrefix hCH).projection _ y) =
    (finalPrefix hCH).projection _ y at hf
  rw [hf]
  exact selected_projection hCH a r y

private theorem map_setCongr_heq {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (s : @SignedMeasure C (borel C)) (t : @SignedMeasure D (borel D))
    (hst : HEq s t) :
    letI : MeasurableSpace C := borel C
    letI : MeasurableSpace D := borel D
    s.map (Homeomorph.setCongr h) = t := by
  subst D
  cases eq_of_heq hst
  exact VectorMeasure.map_id s

/-- Every complete arbitrary signed norm-one lift sequence at the same eta
obeys the fixed parity estimates on the literal finalPrefix successor. -/
theorem quantitative_g (a : Stage)
    (s : ℕ → SignedMeasure ((finalPrefix hCH).Space (nextStage a).1))
    (hmap : ∀ n, (s n).map
      ((finalPrefix hCH).map (eventRow hCH a).1 (nextStage a).1
        ((eventRow_le hCH a).trans (Order.le_succ (ord a)))) =
      (actualBirth hCH (eventRow hCH a)).measure (eta hCH a) n)
    (hmass : ∀ n, (s n).totalVariation univ = 1) (q : ℕ) :
    (q % 2 = 0 → (1 : ℝ) / 6 < s (column hCH a q) (clopen hCH a)) ∧
    (q % 2 ≠ 0 → s (column hCH a q) (clopen hCH a) = 0) := by
  let X := SignedOrdinalHistory.run hCH a
  let E := successorHomeomorph hCH a
  let r : Rows (ord a) := ⟨ord (eventRow hCH a), (eventRow hCH a).2, eventRow_le hCH a⟩
  let Erow := Homeomorph.setCongr (carrier_read hCH a (rowIndex r))
  let p := (finalPrefix hCH).map (eventRow hCH a).1 (nextStage a).1
    ((eventRow_le hCH a).trans (Order.le_succ (ord a)))
  have hr : X.event.selected.treatment.row = r := Subtype.ext (selected_target hCH a).1
  have hm (n : ℕ) :
      ((s n).map E).map (X.event.result.literalProjection X.event.selected.treatment.row) =
        X.event.Q.measure X.event.selected.treatment.row X.event.selected.treatment.label n := by
    rw [hr]
    have hμ : ((actualBirth hCH (eventRow hCH a)).measure (eta hCH a) n).map Erow =
        X.event.Q.measure r X.event.selected.treatment.label n := by
      apply map_setCongr_heq
      have hh := selected_measure hCH a n
      change HEq ((actualBirth hCH (eventRow hCH a)).measure (eta hCH a) n)
        (X.event.Q.measure X.event.selected.treatment.row X.event.selected.treatment.label n) at hh
      rw [hr] at hh
      exact hh
    rw [← hμ, ← hmap n]
    apply VectorMeasure.ext
    intro A hA
    rw [VectorMeasure.map_apply _ (X.event.result.literalProjection r).continuous.measurable hA,
      VectorMeasure.map_apply _ E.continuous.measurable
        ((X.event.result.literalProjection r).continuous.measurable hA),
      VectorMeasure.map_apply _ Erow.continuous.measurable hA,
      VectorMeasure.map_apply _ p.continuous.measurable (Erow.continuous.measurable hA)]
    congr 1
    ext x
    exact eq_iff_iff.mp (congrArg (fun y => y ∈ A) (local_projection hCH a r x))
  have hn (n : ℕ) : SignedMeasure.totalVariation ((s n).map E) univ = 1 := by
    have hv : ((s n).map E).variation = (s n).variation.map E :=
      E.toMeasurableEquiv.measurableEmbedding.variation_map
    rw [SignedMeasure.totalVariation_eq_variation, hv,
      Measure.map_apply E.continuous.measurable MeasurableSet.univ, preimage_univ,
      ← SignedMeasure.totalVariation_eq_variation, hmass n]
  have he (n : ℕ) : ((s n).map E) X.event.result.quantitativeClopen = s n (clopen hCH a) :=
    VectorMeasure.map_apply _ E.continuous.measurable
      X.event.result.quantitativeClopen.isClopen.isClosed.measurableSet
  have hg := X.event.result.quantitative_g q ((s (column hCH a q)).map E)
    (hm (column hCH a q)) (hn (column hCH a q))
  rw [he (column hCH a q)] at hg
  exact hg

/-- Both value sets are infinite for every such signed sequence. In particular,
this applies to every regular signed lift sequence, without any positivity. -/
theorem infinite_values (a : Stage)
    (s : ℕ → SignedMeasure ((finalPrefix hCH).Space (nextStage a).1))
    (hmap : ∀ n, (s n).map
      ((finalPrefix hCH).map (eventRow hCH a).1 (nextStage a).1
        ((eventRow_le hCH a).trans (Order.le_succ (ord a)))) =
      (actualBirth hCH (eventRow hCH a)).measure (eta hCH a) n)
    (hmass : ∀ n, (s n).totalVariation univ = 1) :
    {n | (1 : ℝ) / 6 ≤ s n (clopen hCH a)}.Infinite ∧
      {n | s n (clopen hCH a) = 0}.Infinite := by
  have heven : Injective (fun k : ℕ => column hCH a (2 * k)) :=
    (column_strictMono hCH a).injective.comp (fun x y h => by omega)
  have hodd : Injective (fun k : ℕ => column hCH a (2 * k + 1)) :=
    (column_strictMono hCH a).injective.comp (fun x y h => by omega)
  constructor
  · apply (Set.infinite_range_of_injective heven).mono
    rintro _ ⟨k, rfl⟩
    exact ((quantitative_g hCH a s hmap hmass (2 * k)).1 (by omega)).le
  · apply (Set.infinite_range_of_injective hodd).mono
    rintro _ ⟨k, rfl⟩
    exact (quantitative_g hCH a s hmap hmass (2 * k + 1)).2 (by omega)

end D5.S3.Topology.InverseLimit.SignedOrdinalActualG
