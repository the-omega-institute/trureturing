/- GID: D5/S3/Observer/MetricGeometry/FiniteWordDistanceThreshold
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/FiniteWordDistanceThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite readout agreement is exactly a discrete prediction-distance threshold. -/

import D5.S3.Observer.MetricGeometry.DiscretePredictionUltrametric
import D5.S3.Observer.MetricGeometry.FiniteWordFiberDiameter

/- Library-search audit trail (2026-08-15):
   * Loogle found no declaration named for discounted prediction distance, and
     LeanSearch returned only unrelated finite-product supremum metrics for the
     full statement shape.
   * Both services returned the exact geometric-decay result
     `pow_lt_pow_right_of_lt_one₀`; the proof also applies mathlib's `le_ciSup`.
   * The forward implication imports and applies the repository theorem
     `finite_word_fiber_prediction_diameter`; repository and formalization
     searches found no duplicate of the biconditional below. -/

namespace D5.S3.Observer.MetricGeometry.FiniteWordDistanceThreshold

open BellmanMaxEquation DiscretePredictionUltrametric FiniteWordFiberDiameter

/-- Two states have the same first `m + 1` discrete readouts exactly when their
discounted prediction distance is at most the next geometric scale. -/
theorem finite_word_equivalent_iff_prediction_distance_le
    {Y O : Type*} [DecidableEq O]
    (update : Y -> Y)
    (readout : Y -> O)
    (gamma : Real)
    (hgamma : gamma ∈ Set.Ioo 0 1)
    (m : Nat) (y y' : Y) :
    (∀ k ≤ m,
      readout ((update^[k]) y) = readout ((update^[k]) y')) ↔
    discountedPredictionDistance update readout discreteOutputDistance gamma y y' ≤
      gamma ^ (m + 1) := by
  constructor
  · intro hprefix
    have hself : ∀ a : O, discreteOutputDistance a a = 0 := by
      intro a
      simp [discreteOutputDistance]
    have hbounded : ∀ a b : O, discreteOutputDistance a b ≤ 1 := by
      intro a b
      by_cases h : a = b <;> simp [discreteOutputDistance, h]
    simpa only [mul_one] using
      finite_word_fiber_prediction_diameter
        (update := update) (readout := readout)
        (distance := discreteOutputDistance)
        (gamma := gamma) (bound := 1)
        ⟨hgamma.1, hgamma.2.le⟩ hself hbounded m y y' hprefix
  · intro hdistance k hk
    by_contra hreadout
    have hterms_bddAbove :
        BddAbove (Set.range fun j : Nat =>
          gamma ^ j *
            discreteOutputDistance (readout ((update^[j]) y))
              (readout ((update^[j]) y'))) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨j, rfl⟩
      have houtput_nonnegative :
          0 ≤ discreteOutputDistance (readout ((update^[j]) y))
            (readout ((update^[j]) y')) := by
        by_cases h : readout ((update^[j]) y) = readout ((update^[j]) y') <;>
          simp [discreteOutputDistance, h]
      calc
        gamma ^ j *
            discreteOutputDistance (readout ((update^[j]) y))
              (readout ((update^[j]) y')) ≤
            1 * discreteOutputDistance (readout ((update^[j]) y))
              (readout ((update^[j]) y')) :=
          mul_le_mul_of_nonneg_right
            (pow_le_one₀ hgamma.1.le hgamma.2.le) houtput_nonnegative
        _ = discreteOutputDistance (readout ((update^[j]) y))
              (readout ((update^[j]) y')) := one_mul _
        _ ≤ 1 := by
          by_cases h : readout ((update^[j]) y) = readout ((update^[j]) y') <;>
            simp [discreteOutputDistance, h]
    have hterm_eq :
        gamma ^ k *
            discreteOutputDistance (readout ((update^[k]) y))
              (readout ((update^[k]) y')) = gamma ^ k := by
      simp [discreteOutputDistance, hreadout]
    have hterm_le :
        gamma ^ k *
            discreteOutputDistance (readout ((update^[k]) y))
              (readout ((update^[k]) y')) ≤
          discountedPredictionDistance update readout discreteOutputDistance
            gamma y y' := by
      unfold discountedPredictionDistance
      exact le_ciSup hterms_bddAbove k
    have hpower_le : gamma ^ k ≤ gamma ^ (m + 1) := by
      calc
        gamma ^ k =
            gamma ^ k *
              discreteOutputDistance (readout ((update^[k]) y))
                (readout ((update^[k]) y')) := hterm_eq.symm
        _ ≤ discountedPredictionDistance update readout discreteOutputDistance
              gamma y y' := hterm_le
        _ ≤ gamma ^ (m + 1) := hdistance
    have hstrict : gamma ^ (m + 1) < gamma ^ k :=
      pow_lt_pow_right_of_lt_one₀ hgamma.1 hgamma.2 (by omega)
    exact (not_lt_of_ge hpower_le) hstrict

-- A two-state system with unequal initial readouts witnesses the domain and
-- the strict discount hypothesis; Lean checks that both sides are false.
example :
    ¬(∀ k ≤ 0, id ((id^[k]) false) = id ((id^[k]) true)) ∧
      ¬discountedPredictionDistance id id discreteOutputDistance
          ((1 : Real) / 2) false true ≤
        ((1 : Real) / 2) ^ (0 + 1) := by
  have hgamma : ((1 : Real) / 2) ∈ Set.Ioo 0 1 := by
    constructor <;> norm_num
  constructor
  · intro hprefix
    have hfalse := hprefix 0 (by omega)
    norm_num at hfalse
  · intro hthreshold
    have hprefix :=
      (finite_word_equivalent_iff_prediction_distance_le
        (Y := Bool) (O := Bool) id id ((1 : Real) / 2) hgamma 0 false true).mpr
        hthreshold
    have hfalse := hprefix 0 (by omega)
    norm_num at hfalse

end D5.S3.Observer.MetricGeometry.FiniteWordDistanceThreshold
