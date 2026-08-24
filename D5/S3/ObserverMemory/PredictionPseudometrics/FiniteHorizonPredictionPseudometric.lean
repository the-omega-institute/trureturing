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
     found exact lemmas `Fin.dist_insertNth_insertNth`, `dist_le_pi_dist`,
     `dist_pi_le_iff`, `Finset.sup'_le`, and `Finset.le_sup'`; the finite proof
     applies them directly and needs no global output bound. `Fin (T + 1)` and
     `Finset.univ_nonempty` place finiteness and nonemptiness in the index type.
     Only the separate infinite-supremum theorem retains `hbound`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.PredictionPseudometrics.FiniteHorizonPredictionPseudometric

open D5.S3.Observer.MetricGeometry.BellmanMaxEquation
open D5.S3.Observer.MetricGeometry.FinitePredictionTruncation
open D5.S3.Observer.MetricGeometryLaws.DiscountedPredictionPseudometric
open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

private theorem future_readout_word_succ
    {Y O : Type*} [MetricSpace O]
    (update : Y -> Y) (readout : Y -> O)
    (T : Nat) (y : Y) :
    futureReadoutWord update readout (T + 1) y =
      Fin.insertNth 0 (readout y)
        (futureReadoutWord update readout T (update y)) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [futureReadoutWord]
  · simp [futureReadoutWord, Function.iterate_succ_apply]

private theorem finite_prediction_distance_eq_word_distance
    {Y O : Type*} [MetricSpace O]
    (update : Y -> Y) (readout : Y -> O)
    (T : Nat) (y y' : Y) :
    finitePredictionDistance update readout dist 1 (T + 1) y y' =
      dist (futureReadoutWord update readout T y)
        (futureReadoutWord update readout T y') := by
  induction T generalizing y y' with
  | zero =>
      simp [finitePredictionDistance, futureReadoutWord, dist_pi_def]
  | succ T ih =>
      rw [finitePredictionDistance]
      simp only [one_mul]
      rw [ih]
      rw [future_readout_word_succ update readout T y]
      rw [future_readout_word_succ update readout T y']
      simpa using (Fin.dist_insertNth_insertNth
        (α := fun _ : Fin (T + 2) => O) (0 : Fin (T + 2))
        (readout y) (readout y')
        (futureReadoutWord update readout T (update y))
        (futureReadoutWord update readout T (update y'))).symm

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
  have hzero : finitePredictionDistance id Prod.fst dist 1 (T + 1) x y = 0 := by
    rw [finite_prediction_distance_eq_word_distance id Prod.fst T x y]
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
future agreement, and a finite hidden coordinate can be far apart while
observer influence vanishes. No inhabitant or global output bound is needed. -/
theorem finite_horizon_prediction_pseudometric
    {Y O : Type*} [MetricSpace O]
    (update : Y -> Y) (readout : Y -> O)
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
    (∃ x : PUnit × Fin 101, ∃ y : PUnit × Fin 101,
      Nat.dist (x.2 : Nat) (y.2 : Nat) = 100 /\
      finitePredictionDistance id Prod.fst dist 1 (T + 1) x y = 0 /\
      finitePredictionDistance id Prod.fst dist 1 (T + 1) x y < (100 : Real)) := by
  have hformula : forall y y',
      finitePredictionDistance update readout dist 1 (T + 1) y y' =
        Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (T + 1) =>
          dist (readout ((update^[k]) y)) (readout ((update^[k]) y'))) := by
    intro y y'
    rw [finite_prediction_distance_eq_word_distance update readout T y y']
    have hsupNonnegative :
        0 <= Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (T + 1) =>
          dist (readout ((update^[k]) y)) (readout ((update^[k]) y'))) := by
      exact dist_nonneg.trans (Finset.le_sup'
        (s := Finset.univ)
        (f := fun k : Fin (T + 1) =>
          dist (readout ((update^[k]) y)) (readout ((update^[k]) y')))
        (Finset.mem_univ (0 : Fin (T + 1))))
    apply le_antisymm
    · apply (dist_pi_le_iff hsupNonnegative).2
      intro k
      exact Finset.le_sup' (f := fun j : Fin (T + 1) =>
        dist (readout ((update^[j]) y)) (readout ((update^[j]) y')))
        (Finset.mem_univ k)
    · apply Finset.sup'_le
      intro k _
      exact dist_le_pi_dist
        (futureReadoutWord update readout T y)
        (futureReadoutWord update readout T y') k
  have hfiniteZero : forall y y',
      finitePredictionDistance update readout dist 1 (T + 1) y y' = 0 <->
        (y, y') ∈ finiteFutureRelation update readout T := by
    intro y y'
    rw [finite_prediction_distance_eq_word_distance update readout T y y', dist_eq_zero]
    simp only [finiteFutureRelation, Set.mem_setOf_eq]
    constructor
    · intro hword k hk
      simpa only [futureReadoutWord, observedAt] using
        congrFun hword ⟨k, Nat.lt_succ_of_le hk⟩
    · intro hfuture
      funext k
      simpa only [futureReadoutWord, observedAt] using
        hfuture k (Nat.le_of_lt_succ k.isLt)
  refine ⟨hformula, ?_, ?_, ?_, hfiniteZero,
    raw_distance_large_prediction_distance_zero T⟩
  · intro y
    rw [finite_prediction_distance_eq_word_distance update readout T y y]
    exact dist_self _
  · intro y y'
    rw [finite_prediction_distance_eq_word_distance update readout T y y']
    rw [finite_prediction_distance_eq_word_distance update readout T y' y]
    exact dist_comm _ _
  · intro y y' y''
    rw [finite_prediction_distance_eq_word_distance update readout T y y']
    rw [finite_prediction_distance_eq_word_distance update readout T y y'']
    rw [finite_prediction_distance_eq_word_distance update readout T y'' y']
    exact dist_triangle _ _ _

/-- Under a global output-distance bound, zero undiscounted infinite prediction
distance is exactly infinite future agreement, equivalently equality in the
kernel of the complete itinerary. -/
theorem bounded_infinite_horizon_prediction_zero_kernel
    {Y O : Type*} [MetricSpace O]
    (update : Y -> Y) (readout : Y -> O)
    (bound : Real) (hbound : forall a b : O, dist a b <= bound) :
    (forall y y',
      discountedPredictionDistance update readout dist 1 y y' = 0 <->
        (y, y') ∈ infiniteFutureRelation update readout) /\
    (forall y y',
      discountedPredictionDistance update readout dist 1 y y' = 0 <->
        Setoid.ker (completeItinerary update readout) y y') := by
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
  constructor
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

/-- The public finite theorem applies to an empty state space. -/
example (T : Nat) :
    forall y : Empty,
      finitePredictionDistance (fun x : Empty => (Empty.elim x : Empty))
        (fun x : Empty => (Empty.elim x : Real)) dist 1 (T + 1) y y = 0 := by
  exact (finite_horizon_prediction_pseudometric.{0, 0, 0}
    (Y := Empty) (O := Real)
    (fun x => Empty.elim x) (fun x => Empty.elim x) T).2.1

/-- The public finite theorem applies to a real-valued observer even though
the ambient real metric admits no global distance bound. -/
example :
    finitePredictionDistance (id : Bool -> Bool)
        (fun b => if b then (1 : Real) else 0) dist 1 1 false true = 1 /\
      ¬ ∃ bound : Real, forall a b : Real, dist a b <= bound := by
  constructor
  · have hformula := (finite_horizon_prediction_pseudometric.{0, 0, 0}
      (Y := Bool) (O := Real) id
      (fun b => if b then (1 : Real) else 0) 0).1 false true
    calc
      finitePredictionDistance (id : Bool -> Bool)
          (fun b => if b then (1 : Real) else 0) dist 1 1 false true =
          Finset.univ.sup' Finset.univ_nonempty (fun k : Fin 1 =>
            dist ((fun b => if b then (1 : Real) else 0) ((id^[k]) false))
              ((fun b => if b then (1 : Real) else 0) ((id^[k]) true))) := hformula
      _ = 1 := by norm_num [Real.dist_eq]
  · rintro ⟨bound, hbound⟩
    have hnonnegative : 0 <= bound := by simpa using hbound 0 0
    have hfar := hbound (bound + 1) 0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)] at hfar
    linarith

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
#print axioms bounded_infinite_horizon_prediction_zero_kernel

end D5.S3.ObserverMemory.PredictionPseudometrics.FiniteHorizonPredictionPseudometric
