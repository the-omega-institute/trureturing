/- GID: D5/S3/Observer/MetricGeometry/FinitePredictionTruncation
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/FinitePredictionTruncation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Bellman prediction distances have an exact maximum formula and geometric error. -/

import D5.S3.Observer.MetricGeometry.BellmanMaxEquation
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-15):
   * Loogle returned `Finset.max_le_iff`, but inspection showed that it concerns
     `WithBot`-valued `Finset.max`, not the real-valued nonempty supremum here.
     It also returned the indexed-supremum support results `le_iSup` and
     `le_iSup_of_le`. A natural-language query was rejected as invalid syntax.
   * LeanSearch returned `Finset.le_sup'_of_le`, `Finset.sup'_le`, and nearby
     geometric-series/truncation results, but no full finite Bellman truncation
     theorem. Its documented POST endpoint was used after an initial GET miss.
   * The proof imports and applies the exact library theorem
     `max_sub_max_le_max`, as well as `Finset.sup'_univ_eq_ciSup`, `le_ciSup`,
     `ciSup_le`, and `pow_le_pow_of_le_one`. Repository and formalization-record
     searches found no equal-or-stronger declaration. -/

namespace D5.S3.Observer.MetricGeometry.FinitePredictionTruncation

open BellmanMaxEquation

/-- The finite-horizon Bellman iteration, starting from the zero discrepancy. -/
def finitePredictionDistance
    {Y O : Type*}
    (update : Y -> Y)
    (readout : Y -> O)
    (distance : O -> O -> Real)
    (gamma : Real) : Nat -> Y -> Y -> Real
  | 0, _, _ => 0
  | n + 1, y, y' =>
      max (distance (readout y) (readout y'))
        (gamma * finitePredictionDistance update readout distance gamma n
          (update y) (update y'))

private theorem finite_iSup_succ
    {Y O : Type*}
    (update : Y -> Y)
    (readout : Y -> O)
    (distance : O -> O -> Real)
    (gamma : Real)
    (hgamma : 0 <= gamma)
    (m : Nat) (y y' : Y) :
    (⨆ k : Fin (m + 2),
      gamma ^ (k : Nat) *
        distance (readout ((update^[k]) y)) (readout ((update^[k]) y'))) =
      max (distance (readout y) (readout y'))
        (gamma * (⨆ k : Fin (m + 1),
          gamma ^ (k : Nat) *
            distance (readout ((update^[k]) (update y)))
              (readout ((update^[k]) (update y'))))) := by
  let fullTerm : Fin (m + 2) -> Real := fun k =>
    gamma ^ (k : Nat) *
      distance (readout ((update^[k]) y)) (readout ((update^[k]) y'))
  let tailTerm : Fin (m + 1) -> Real := fun k =>
    gamma ^ (k : Nat) *
      distance (readout ((update^[k]) (update y)))
        (readout ((update^[k]) (update y')))
  have hfull : BddAbove (Set.range fullTerm) := Set.Finite.bddAbove (Set.finite_range _)
  have htail : BddAbove (Set.range tailTerm) := Set.Finite.bddAbove (Set.finite_range _)
  change (⨆ k, fullTerm k) =
    max (distance (readout y) (readout y')) (gamma * ⨆ k, tailTerm k)
  apply le_antisymm
  · apply ciSup_le
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [fullTerm]
    · calc
        fullTerm j.succ = gamma * tailTerm j := by
          simp [fullTerm, tailTerm, pow_succ', Function.iterate_succ_apply, mul_assoc]
        _ <= gamma * (⨆ i, tailTerm i) :=
          mul_le_mul_of_nonneg_left (le_ciSup htail j) hgamma
        _ <= max (distance (readout y) (readout y')) (gamma * ⨆ i, tailTerm i) :=
          le_max_right _ _
  · apply max_le
    · simpa [fullTerm] using (le_ciSup hfull (0 : Fin (m + 2)))
    · rw [Real.mul_iSup_of_nonneg hgamma]
      apply ciSup_le
      intro k
      calc
        gamma * tailTerm k = fullTerm k.succ := by
          simp [fullTerm, tailTerm, pow_succ', Function.iterate_succ_apply, mul_assoc]
        _ <= ⨆ i, fullTerm i := le_ciSup hfull k.succ

private theorem finite_prediction_distance_formula
    {Y O : Type*}
    (update : Y -> Y)
    (readout : Y -> O)
    (distance : O -> O -> Real)
    (gamma : Real)
    (hgamma : 0 <= gamma)
    (hdistance : forall a b, 0 <= distance a b)
    (m : Nat) (y y' : Y) :
    finitePredictionDistance update readout distance gamma (m + 1) y y' =
      ⨆ k : Fin (m + 1),
        gamma ^ (k : Nat) *
          distance (readout ((update^[k]) y)) (readout ((update^[k]) y')) := by
  induction m generalizing y y' with
  | zero =>
      simp [finitePredictionDistance, hdistance]
  | succ m ih =>
      rw [finitePredictionDistance, ih (update y) (update y')]
      exact (finite_iSup_succ update readout distance gamma hgamma m y y').symm

private theorem finite_prediction_distance_error
    {Y O : Type*}
    (update : Y -> Y)
    (readout : Y -> O)
    (distance : O -> O -> Real)
    (gamma bound : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (hdistance : forall a b, distance a b ∈ Set.Icc 0 bound) :
    forall n y y',
      0 <= discountedPredictionDistance update readout distance gamma y y' -
        finitePredictionDistance update readout distance gamma n y y' ∧
      discountedPredictionDistance update readout distance gamma y y' -
          finitePredictionDistance update readout distance gamma n y y' <=
        gamma ^ n * bound := by
  intro n
  induction n with
  | zero =>
      intro y y'
      have hterms : BddAbove (Set.range fun k : Nat =>
          gamma ^ k *
            distance (readout ((update^[k]) y)) (readout ((update^[k]) y'))) := by
        refine ⟨bound, ?_⟩
        rintro _ ⟨k, rfl⟩
        calc
          gamma ^ k *
              distance (readout ((update^[k]) y)) (readout ((update^[k]) y')) <=
              1 * distance (readout ((update^[k]) y))
                (readout ((update^[k]) y')) :=
            mul_le_mul_of_nonneg_right
              (pow_le_one₀ hgamma.1.le hgamma.2) (hdistance _ _).1
          _ <= bound := by simpa using (hdistance _ _).2
      constructor
      · simp only [finitePredictionDistance, sub_zero]
        unfold discountedPredictionDistance
        exact (mul_nonneg (pow_nonneg hgamma.1.le 0) (hdistance _ _).1).trans
          (le_ciSup hterms 0)
      · simp only [finitePredictionDistance, sub_zero, pow_zero, one_mul]
        unfold discountedPredictionDistance
        exact ciSup_le fun k => by
          calc
            gamma ^ k *
                distance (readout ((update^[k]) y)) (readout ((update^[k]) y')) <=
                1 * distance (readout ((update^[k]) y))
                  (readout ((update^[k]) y')) :=
              mul_le_mul_of_nonneg_right
                (pow_le_one₀ hgamma.1.le hgamma.2) (hdistance _ _).1
            _ <= bound := by simpa using (hdistance _ _).2
  | succ n ih =>
      intro y y'
      have hnext := ih (update y) (update y')
      have hbellman := discounted_prediction_distance_bellman
        update readout distance gamma bound hgamma hdistance y y'
      rw [finitePredictionDistance, hbellman]
      constructor
      · apply sub_nonneg.mpr
        apply max_le_max_left
        exact mul_le_mul_of_nonneg_left (sub_nonneg.mp hnext.1) hgamma.1.le
      · calc
          max (distance (readout y) (readout y'))
                (gamma * discountedPredictionDistance update readout distance gamma
                  (update y) (update y')) -
              max (distance (readout y) (readout y'))
                (gamma * finitePredictionDistance update readout distance gamma n
                  (update y) (update y')) <=
              max
                (distance (readout y) (readout y') - distance (readout y) (readout y'))
                (gamma * discountedPredictionDistance update readout distance gamma
                    (update y) (update y') -
                  gamma * finitePredictionDistance update readout distance gamma n
                    (update y) (update y')) :=
            max_sub_max_le_max _ _ _ _
          _ = gamma *
              (discountedPredictionDistance update readout distance gamma
                  (update y) (update y') -
                finitePredictionDistance update readout distance gamma n
                  (update y) (update y')) := by
            rw [sub_self, mul_sub, max_eq_right]
            simpa [mul_sub] using mul_nonneg hgamma.1.le hnext.1
          _ <= gamma * (gamma ^ n * bound) :=
            mul_le_mul_of_nonneg_left hnext.2 hgamma.1.le
          _ = gamma ^ (n + 1) * bound := by
            rw [pow_succ']
            ring

/-- The `(m + 1)`st finite Bellman iterate is the maximum of the first
`m + 1` discounted discrepancies, and its error is at most the next geometric
scale times the global discrepancy bound. -/
theorem finite_prediction_truncation_formula_and_error
    {Y O : Type*}
    (update : Y -> Y)
    (readout : Y -> O)
    (distance : O -> O -> Real)
    (gamma bound : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (hdistance : forall a b, distance a b ∈ Set.Icc 0 bound)
    (m : Nat) (y y' : Y) :
    finitePredictionDistance update readout distance gamma (m + 1) y y' =
        Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (m + 1) =>
          gamma ^ (k : Nat) *
            distance (readout ((update^[k]) y)) (readout ((update^[k]) y'))) ∧
      0 <= discountedPredictionDistance update readout distance gamma y y' -
        finitePredictionDistance update readout distance gamma (m + 1) y y' ∧
      discountedPredictionDistance update readout distance gamma y y' -
          finitePredictionDistance update readout distance gamma (m + 1) y y' <=
        gamma ^ (m + 1) * bound := by
  constructor
  · rw [Finset.sup'_univ_eq_ciSup]
    exact finite_prediction_distance_formula update readout distance gamma
      hgamma.1.le (fun a b => (hdistance a b).1) m y y'
  · exact finite_prediction_distance_error update readout distance gamma bound
      hgamma hdistance (m + 1) y y'

-- A one-state system with unit discrepancy witnesses every clause and hypothesis.
example (m : Nat) :
    finitePredictionDistance id (fun _ : Unit => ()) (fun _ _ => (1 : Real))
        ((1 : Real) / 2) (m + 1) () () =
        Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (m + 1) =>
          ((1 : Real) / 2) ^ (k : Nat)) ∧
      0 <= discountedPredictionDistance id (fun _ : Unit => ())
        (fun _ _ => (1 : Real)) ((1 : Real) / 2) () () -
          finitePredictionDistance id (fun _ : Unit => ()) (fun _ _ => (1 : Real))
            ((1 : Real) / 2) (m + 1) () () ∧
      discountedPredictionDistance id (fun _ : Unit => ())
          (fun _ _ => (1 : Real)) ((1 : Real) / 2) () () -
          finitePredictionDistance id (fun _ : Unit => ()) (fun _ _ => (1 : Real))
            ((1 : Real) / 2) (m + 1) () () <=
        ((1 : Real) / 2) ^ (m + 1) := by
  have hgamma : ((1 : Real) / 2) ∈ Set.Ioc 0 1 := by
    constructor <;> norm_num
  have hdistance : forall _ _ : Unit, (1 : Real) ∈ Set.Icc 0 1 := by
    intro _ _
    exact ⟨zero_le_one, le_rfl⟩
  simpa only [id_eq, mul_one, Function.iterate_id, Function.id_def] using
    finite_prediction_truncation_formula_and_error
      (Y := Unit) (O := Unit) id (fun _ => ()) (fun _ _ => (1 : Real))
        ((1 : Real) / 2) 1 hgamma hdistance m () ()

end D5.S3.Observer.MetricGeometry.FinitePredictionTruncation
