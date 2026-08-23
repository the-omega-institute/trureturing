/- GID: D5/S3/ObserverMemory/PredictionPseudometrics/FiniteHorizonPredictionPseudometric
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionPseudometrics/FiniteHorizonPredictionPseudometric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite prediction distance is a pseudometric whose kernel is finite future agreement. -/

import D5.S3.Observer.MetricGeometry.FinitePredictionTruncation
import D5.S3.Observer.MetricGeometryLaws.DiscountedPredictionPseudometric
import D5.S3.Observer.Separation.FiniteFutureCongruence
import D5.S3.ObserverMemory.Prediction.ItineraryCompletion
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'finite_horizon_prediction_pseudometric' D5
     Golden/Frozen/accepted` exited 1 with no existing declaration.
   * Type-shape search `rg -n 'BddAbove.*dist|sSup.*dist|iSup.*dist|
     Finset\\.(sup|sup\\x27|max\\x27).*dist|Set \\(X × X\\)' D5` found the
     canonical `finitePredictionDistance` and its public finite-supremum formula
     in `FinitePredictionTruncation`, plus the canonical discounted supremum in
     `BellmanMaxEquation`; both are imported and reused, so no distance is
     redeclared here. The pair-set hits included `defectRelation`, but this file
     introduces no target-defect or other pair-set definition.
   * Mathematical-synonym search `rg -n -i 'prediction|predictive|future|
     trajectory|orbit|pseudometric|semimetric|zero kernel|kernel|completion|
     readout|observer' D5/S3/ObserverMemory D5/S3/ConceptDynamics` found
     `finiteFutureRelation`, `infiniteFutureRelation`, `completeItinerary`, and
     `discounted_prediction_pseudometric`. They are imported and applied below;
     none packages the finite formula, its pseudometric laws, both zero-kernel
     identifications, and the raw-versus-observer witness in one theorem.
   * Neighbor-vocabulary search `git grep -n '^def \\|^  def ' --
     D5/S3/ObserverMemory | head -60`, after listing every immediate subdomain,
     found `futureReadoutWord` and the existing prediction relations/itinerary
     vocabulary. The proof uses those names rather than declaring synonyms.
   * Pinned Mathlib search for finite product distances and nonempty suprema
     found exact lemmas `dist_pi_def`, `dist_le_pi_dist`, `dist_pi_le_iff`,
     `Finset.sup'_le`, and `Finset.le_sup'`; the proof applies the latter four
     directly. `Fin (T + 1)` and `Finset.univ_nonempty` place finiteness and
     nonemptiness in the statement's types, while `hbound` supplies boundedness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.PredictionPseudometrics.FiniteHorizonPredictionPseudometric

open D5.S3.Observer.MetricGeometry.BellmanMaxEquation
open D5.S3.Observer.MetricGeometry.FinitePredictionTruncation
open D5.S3.Observer.MetricGeometryLaws.DiscountedPredictionPseudometric
open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

private theorem finite_prediction_distance_eq_word_distance
    {Y O : Type*} [MetricSpace O]
    (update : Y -> Y) (readout : Y -> O)
    (bound : Real) (hbound : forall a b : O, dist a b <= bound)
    (T : Nat) (y y' : Y) :
    finitePredictionDistance update readout dist 1 (T + 1) y y' =
      dist (futureReadoutWord update readout T y)
        (futureReadoutWord update readout T y') := by
  have hformula :=
    (finite_prediction_truncation_formula_and_error
      update readout dist 1 bound (by constructor <;> norm_num)
      (fun a b => ⟨dist_nonneg, hbound a b⟩) T y y').1
  rw [hformula]
  simp only [one_pow, one_mul]
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    exact dist_le_pi_dist
      (futureReadoutWord update readout T y)
      (futureReadoutWord update readout T y') k
  · have hsupNonnegative :
        0 <= Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (T + 1) =>
          dist (readout ((update^[k]) y)) (readout ((update^[k]) y'))) := by
      exact dist_nonneg.trans (Finset.le_sup'
        (s := Finset.univ)
        (f := fun k : Fin (T + 1) =>
          dist (readout ((update^[k]) y)) (readout ((update^[k]) y')))
        (Finset.mem_univ (0 : Fin (T + 1))))
    apply (dist_pi_le_iff hsupNonnegative).2
    intro k
    exact Finset.le_sup' (f := fun j : Fin (T + 1) =>
      dist (readout ((update^[j]) y)) (readout ((update^[j]) y')))
      (Finset.mem_univ k)

private theorem infinite_prediction_zero_iff_complete_itinerary
    {Y O : Type*} [MetricSpace O]
    (update : Y -> Y) (readout : Y -> O)
    (bound : Real) (hbound : forall a b : O, dist a b <= bound)
    (y y' : Y) :
    discountedPredictionDistance update readout dist 1 y y' = 0 <->
      completeItinerary update readout y =
        completeItinerary update readout y' := by
  have hgamma : (1 : Real) ∈ Set.Ioc 0 1 := by
    constructor <;> norm_num
  have hterms :
      BddAbove (Set.range fun k : Nat =>
        (1 : Real) ^ k *
          dist (readout ((update^[k]) y)) (readout ((update^[k]) y'))) := by
    refine ⟨bound, ?_⟩
    rintro _ ⟨k, rfl⟩
    simpa using hbound (readout ((update^[k]) y)) (readout ((update^[k]) y'))
  constructor
  · intro hzero
    funext k
    apply dist_eq_zero.mp
    apply le_antisymm
    · have hterm :
          dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) <=
            discountedPredictionDistance update readout dist 1 y y' := by
        unfold discountedPredictionDistance
        simpa only [one_pow, one_mul] using le_ciSup hterms k
      exact hterm.trans_eq hzero
    · exact dist_nonneg
  · intro hitinerary
    apply le_antisymm
    · unfold discountedPredictionDistance
      apply ciSup_le
      intro k
      simp only [one_pow, one_mul]
      have hout : readout ((update^[k]) y) = readout ((update^[k]) y') := by
        simpa only [completeItinerary] using congrFun hitinerary k
      simp only [hout, dist_self]
      exact le_rfl
    · exact
        ((discounted_prediction_pseudometric update readout 1 bound hgamma hbound
          y y' y).1.1)

private theorem raw_distance_large_prediction_distance_zero (T : Nat) :
    exists x : PUnit × Fin 101, exists y : PUnit × Fin 101,
      Nat.dist (x.2 : Nat) (y.2 : Nat) = 100 /\
      finitePredictionDistance id Prod.fst dist 1 (T + 1) x y = 0 /\
      finitePredictionDistance id Prod.fst dist 1 (T + 1) x y < (100 : Real) := by
  let x : PUnit × Fin 101 := (PUnit.unit, 0)
  let y : PUnit × Fin 101 := (PUnit.unit, 100)
  have hbound : forall a b : PUnit, dist a b <= (0 : Real) := by
    intro a b
    simp
  have hzero : finitePredictionDistance id Prod.fst dist 1 (T + 1) x y = 0 := by
    rw [finite_prediction_distance_eq_word_distance id Prod.fst 0 hbound T x y]
    apply dist_eq_zero.mpr
    funext k
    change ((id^[k]) x).1 = ((id^[k]) y).1
    simp [x, y]
  refine ⟨x, y, ?_, hzero, ?_⟩
  · norm_num [x, y, Nat.dist]
  · rw [hzero]
    norm_num [x, y, Nat.dist]

/-- The undiscounted finite prediction distance is exactly the maximum output
distance through time `T`. It is a pseudometric, its zero kernel is finite
future agreement, the undiscounted infinite kernel is complete-itinerary
agreement, and a finite hidden coordinate can be far apart while observer
influence vanishes. -/
theorem finite_horizon_prediction_pseudometric
    {Y O : Type*} [Nonempty Y] [MetricSpace O]
    (update : Y -> Y) (readout : Y -> O)
    (bound : Real) (hbound : forall a b : O, dist a b <= bound)
    (T : Nat) :
    (forall y y',
      finitePredictionDistance update readout dist 1 (T + 1) y y' =
        Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (T + 1) =>
          dist (readout ((update^[k]) y)) (readout ((update^[k]) y')))) /\
    (forall y,
      finitePredictionDistance update readout dist 1 (T + 1) y y = 0) /\
    (forall y y',
      finitePredictionDistance update readout dist 1 (T + 1) y y' =
        finitePredictionDistance update readout dist 1 (T + 1) y' y) /\
    (forall y y' y'',
      finitePredictionDistance update readout dist 1 (T + 1) y y' <=
        finitePredictionDistance update readout dist 1 (T + 1) y y'' +
          finitePredictionDistance update readout dist 1 (T + 1) y'' y') /\
    (forall y y',
      finitePredictionDistance update readout dist 1 (T + 1) y y' = 0 <->
        (y, y') ∈ finiteFutureRelation update readout T) /\
    (forall y y',
      discountedPredictionDistance update readout dist 1 y y' = 0 <->
        (y, y') ∈ infiniteFutureRelation update readout) /\
    (forall y y',
      discountedPredictionDistance update readout dist 1 y y' = 0 <->
        Setoid.ker (completeItinerary update readout) y y') /\
    (∃ x : PUnit × Fin 101, ∃ y : PUnit × Fin 101,
      Nat.dist (x.2 : Nat) (y.2 : Nat) = 100 /\
      finitePredictionDistance id Prod.fst dist 1 (T + 1) x y = 0 /\
      finitePredictionDistance id Prod.fst dist 1 (T + 1) x y < (100 : Real)) := by
  have hformula : forall y y',
      finitePredictionDistance update readout dist 1 (T + 1) y y' =
        Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (T + 1) =>
          dist (readout ((update^[k]) y)) (readout ((update^[k]) y'))) := by
    intro y y'
    have h :=
      (finite_prediction_truncation_formula_and_error
        update readout dist 1 bound (by constructor <;> norm_num)
        (fun a b => ⟨dist_nonneg, hbound a b⟩) T y y').1
    simpa only [one_pow, one_mul] using h
  have hfiniteZero : forall y y',
      finitePredictionDistance update readout dist 1 (T + 1) y y' = 0 <->
        (y, y') ∈ finiteFutureRelation update readout T := by
    intro y y'
    rw [finite_prediction_distance_eq_word_distance
      update readout bound hbound T y y', dist_eq_zero]
    simp only [finiteFutureRelation, Set.mem_setOf_eq]
    constructor
    · intro hword k hk
      simpa only [futureReadoutWord, observedAt] using
        congrFun hword ⟨k, Nat.lt_succ_of_le hk⟩
    · intro hfuture
      funext k
      simpa only [futureReadoutWord, observedAt] using
        hfuture k (Nat.le_of_lt_succ k.isLt)
  have hrelationItinerary : forall y y',
      (y, y') ∈ infiniteFutureRelation update readout <->
        completeItinerary update readout y =
          completeItinerary update readout y' := by
    intro y y'
    constructor
    · intro hfuture
      funext k
      simpa only [completeItinerary, observedAt] using hfuture k
    · intro hitinerary k
      simpa only [completeItinerary, observedAt] using congrFun hitinerary k
  refine ⟨hformula, ?_, ?_, ?_, hfiniteZero, ?_, ?_,
    raw_distance_large_prediction_distance_zero T⟩
  · intro y
    rw [finite_prediction_distance_eq_word_distance
      update readout bound hbound T y y]
    exact dist_self _
  · intro y y'
    rw [finite_prediction_distance_eq_word_distance
      update readout bound hbound T y y']
    rw [finite_prediction_distance_eq_word_distance
      update readout bound hbound T y' y]
    exact dist_comm _ _
  · intro y y' y''
    rw [finite_prediction_distance_eq_word_distance
      update readout bound hbound T y y']
    rw [finite_prediction_distance_eq_word_distance
      update readout bound hbound T y y'']
    rw [finite_prediction_distance_eq_word_distance
      update readout bound hbound T y'' y']
    exact dist_triangle _ _ _
  · intro y y'
    exact (infinite_prediction_zero_iff_complete_itinerary
      update readout bound hbound y y').trans (hrelationItinerary y y').symm
  · intro y y'
    simpa only [Setoid.ker_def] using
      infinite_prediction_zero_iff_complete_itinerary
        update readout bound hbound y y'

/-- Distinct visible Boolean states mapped to zero and one have positive
finite prediction distance, so the finite zero kernel is not universally full. -/
example :
    finitePredictionDistance (id : Bool -> Bool)
      (fun b => if b then (1 : Real) else 0) dist 1 1 false true = 1 := by
  norm_num [finitePredictionDistance, Real.dist_eq]

/-- A hidden finite coordinate can have raw displacement one hundred while a
constant visible coordinate gives zero prediction distance. -/
example :
    let x : PUnit × Fin 101 := (PUnit.unit, 0)
    let y : PUnit × Fin 101 := (PUnit.unit, 100)
    Nat.dist (x.2 : Nat) (y.2 : Nat) = 100 /\
      finitePredictionDistance id Prod.fst dist 1 3 x y = 0 := by
  dsimp
  constructor
  · norm_num [Nat.dist]
  · simp [finitePredictionDistance]

#print axioms finite_horizon_prediction_pseudometric

end D5.S3.ObserverMemory.PredictionPseudometrics.FiniteHorizonPredictionPseudometric
