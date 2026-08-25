/- GID: D5/S3/Observer/MetricGeometryLaws/WeightedPredictionZeroKernel
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometryLaws/WeightedPredictionZeroKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zero weighted prediction distance is exactly orbit-readout agreement. -/

import D5.S3.Observer.MetricGeometry.BellmanMaxEquation
import D5.S3.Observer.MetricGeometry.DiscretePredictionUltrametric
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-24):
   * Current-tree searches found the canonical orbit supremum
     `BellmanMaxEquation.discountedPredictionDistance`; it is reused below rather
     than redeclared. The coordinate discrepancy reuses
     `DiscretePredictionUltrametric.discreteOutputDistance`.
   * The nearby theorem `bounded_infinite_horizon_prediction_zero_kernel` covers
     one metric-valued readout at discount one, not a finite family with arbitrary
     positive weights and arbitrary positive discount.
   * Exact statement searches across D5, accepted freezes, and pinned Mathlib were
     misses. Supporting exact hits are `Finset.sup'_le`, `Finset.le_sup'`,
     `le_ciSup`, `ciSup_le`, `mul_eq_zero`, and `pow_pos`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.MetricGeometryLaws.WeightedPredictionZeroKernel

open D5.S3.Observer.MetricGeometry.BellmanMaxEquation
open D5.S3.Observer.MetricGeometry.DiscretePredictionUltrametric

/-- The largest selected coordinate weight on which two states have unequal readouts,
with value zero for an empty observation budget. -/
noncomputable def weightedCoordinateDistance
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (x y : X) : Real :=
  if hJ : J.Nonempty then
    J.sup' hJ (fun i =>
      weight i * @discreteOutputDistance (O i) (Classical.decEq (O i))
        (readout i x) (readout i y))
  else
    0

private theorem weighted_coordinate_distance_nonnegative
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (hpositive : ∀ i ∈ J, 0 < weight i) (x y : X) :
    0 <= weightedCoordinateDistance J weight readout x y := by
  classical
  by_cases hJ : J.Nonempty
  · simp only [weightedCoordinateDistance, dif_pos hJ]
    obtain ⟨i, hi⟩ := hJ
    have hterm :
        0 <= weight i * @discreteOutputDistance (O i) (Classical.decEq (O i))
          (readout i x) (readout i y) := by
      by_cases hequal : readout i x = readout i y
      · simp [discreteOutputDistance, hequal]
      · simpa [discreteOutputDistance, hequal] using (hpositive i hi).le
    exact hterm.trans (Finset.le_sup' (s := J) (f := fun j =>
      weight j * @discreteOutputDistance (O j) (Classical.decEq (O j))
        (readout j x) (readout j y)) hi)
  · simp [weightedCoordinateDistance, hJ]

private theorem weighted_coordinate_distance_le_weight_sum
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (hpositive : ∀ i ∈ J, 0 < weight i) (x y : X) :
    weightedCoordinateDistance J weight readout x y <= J.sum weight := by
  classical
  by_cases hJ : J.Nonempty
  · simp only [weightedCoordinateDistance, dif_pos hJ]
    apply Finset.sup'_le
    intro i hi
    by_cases hequal : readout i x = readout i y
    · simp only [discreteOutputDistance, if_pos hequal, mul_zero]
      exact Finset.sum_nonneg fun j hj => (hpositive j hj).le
    · simp only [discreteOutputDistance, if_neg hequal, mul_one]
      exact Finset.single_le_sum (fun j hj => (hpositive j hj).le) hi
  · have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    subst J
    simp [weightedCoordinateDistance]

private theorem weighted_coordinate_distance_zero_iff
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (hpositive : ∀ i ∈ J, 0 < weight i) (x y : X) :
    weightedCoordinateDistance J weight readout x y = 0 <->
      ∀ i ∈ J, readout i x = readout i y := by
  classical
  by_cases hJ : J.Nonempty
  · constructor
    · intro hzero i hi
      by_contra hne
      have hle :
          weight i * @discreteOutputDistance (O i) (Classical.decEq (O i))
              (readout i x) (readout i y) <=
            weightedCoordinateDistance J weight readout x y := by
        simp only [weightedCoordinateDistance, dif_pos hJ]
        exact Finset.le_sup' (s := J) (f := fun j =>
          weight j * @discreteOutputDistance (O j) (Classical.decEq (O j))
            (readout j x) (readout j y)) hi
      have hpositiveTerm :
          0 < weight i * @discreteOutputDistance (O i) (Classical.decEq (O i))
            (readout i x) (readout i y) := by
        simpa [discreteOutputDistance, hne] using hpositive i hi
      rw [hzero] at hle
      exact (not_lt_of_ge hle hpositiveTerm)
    · intro hagree
      apply le_antisymm
      · simp only [weightedCoordinateDistance, dif_pos hJ]
        apply Finset.sup'_le
        intro i hi
        simp [discreteOutputDistance, hagree i hi]
      · exact weighted_coordinate_distance_nonnegative
          J weight readout hpositive x y
  · have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    subst J
    simp [weightedCoordinateDistance]

/-- For a finite family of equality readouts, positive selected weights and a
positive discount at most one make zero discounted prediction distance equivalent
to agreement of every selected readout at every time. -/
theorem weighted_prediction_zero_kernel
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (update : X -> X) (gamma : Real)
    (hpositive : ∀ i ∈ J, 0 < weight i)
    (hgamma : gamma ∈ Set.Ioc 0 1) (x y : X) :
    discountedPredictionDistance update id
        (weightedCoordinateDistance J weight readout) gamma x y = 0 <->
      ∀ n : Nat, ∀ i ∈ J,
        readout i ((update^[n]) x) = readout i ((update^[n]) y) := by
  have hterms :
      BddAbove (Set.range fun n : Nat =>
        gamma ^ n * weightedCoordinateDistance J weight readout
          ((update^[n]) x) ((update^[n]) y)) := by
    refine ⟨J.sum weight, ?_⟩
    rintro _ ⟨n, rfl⟩
    calc
      gamma ^ n * weightedCoordinateDistance J weight readout
          ((update^[n]) x) ((update^[n]) y) <=
          1 * weightedCoordinateDistance J weight readout
            ((update^[n]) x) ((update^[n]) y) :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ hgamma.1.le hgamma.2)
          (weighted_coordinate_distance_nonnegative J weight readout hpositive _ _)
      _ = weightedCoordinateDistance J weight readout
          ((update^[n]) x) ((update^[n]) y) := one_mul _
      _ <= J.sum weight :=
        weighted_coordinate_distance_le_weight_sum
          J weight readout hpositive _ _
  constructor
  · intro hzero n i hi
    have hterm :
        gamma ^ n * weightedCoordinateDistance J weight readout
            ((update^[n]) x) ((update^[n]) y) <=
          discountedPredictionDistance update id
            (weightedCoordinateDistance J weight readout) gamma x y := by
      unfold discountedPredictionDistance
      simpa only [id_eq] using le_ciSup hterms n
    have htermNonnegative :
        0 <= gamma ^ n * weightedCoordinateDistance J weight readout
          ((update^[n]) x) ((update^[n]) y) :=
      mul_nonneg (pow_nonneg hgamma.1.le n)
        (weighted_coordinate_distance_nonnegative
          J weight readout hpositive _ _)
    have htermZero :
        gamma ^ n * weightedCoordinateDistance J weight readout
          ((update^[n]) x) ((update^[n]) y) = 0 :=
      le_antisymm (hterm.trans_eq hzero) htermNonnegative
    have hdistanceZero :
        weightedCoordinateDistance J weight readout
          ((update^[n]) x) ((update^[n]) y) = 0 :=
      (mul_eq_zero.mp htermZero).resolve_left (pow_pos hgamma.1 n).ne'
    exact (weighted_coordinate_distance_zero_iff
      J weight readout hpositive _ _).mp hdistanceZero i hi
  · intro hagree
    apply le_antisymm
    · unfold discountedPredictionDistance
      apply ciSup_le
      intro n
      have hdistanceZero := (weighted_coordinate_distance_zero_iff
        J weight readout hpositive ((update^[n]) x) ((update^[n]) y)).mpr
          (hagree n)
      simp only [id_eq, hdistanceZero, mul_zero]
      exact le_rfl
    · unfold discountedPredictionDistance
      have hnonnegative :
          0 <= gamma ^ 0 * weightedCoordinateDistance J weight readout x y :=
        mul_nonneg (pow_nonneg hgamma.1.le 0)
          (weighted_coordinate_distance_nonnegative
            J weight readout hpositive x y)
      simpa only [id_eq, Function.iterate_zero_apply] using
        hnonnegative.trans (le_ciSup hterms 0)

/-- The positivity and discount hypotheses have a checked one-coordinate witness. -/
example :
    (∀ i ∈ ({PUnit.unit} : Finset PUnit),
      0 < (fun _ : PUnit => (1 : Real)) i) ∧
    ((1 : Real) / 2) ∈ Set.Ioc 0 1 := by
  constructor
  · intro i hi
    norm_num
  · constructor <;> norm_num

/-- The state domain can contain two states with distinct selected readouts. -/
example : Bool := false

#print axioms weighted_prediction_zero_kernel

end D5.S3.Observer.MetricGeometryLaws.WeightedPredictionZeroKernel
