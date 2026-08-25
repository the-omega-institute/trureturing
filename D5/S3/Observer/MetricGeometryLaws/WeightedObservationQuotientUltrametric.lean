/- GID: D5/S3/Observer/MetricGeometryLaws/WeightedObservationQuotientUltrametric
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometryLaws/WeightedObservationQuotientUltrametric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Weighted equality-readout distance descends to an observation-quotient ultrametric. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import D5.S3.Observer.MetricGeometryLaws.WeightedPredictionZeroKernel

/- Library-search audit trail (2026-08-25):
   * Exact current-tree hits `weightedCoordinateDistance` and `jointReadout`
     supply the source distance and finite dependent-product readout; neither
     is redeclared.
   * The static zero-kernel helper in `WeightedPredictionZeroKernel` is private,
     while its public theorem concerns every time of a dynamic orbit. Thus it
     is not an exact bind hit for this static theorem and quotient conclusion.
   * Body-shape searches found no quotient lift of `weightedCoordinateDistance`.
     The only D5 binary quotient lift concerns an unrelated refinement relation.
   * Pinned Mathlib exact hits `Quotient.liftOn₂`, `Quotient.sound`,
     `Quotient.exact`, `Finset.sup'_congr`, `Finset.sup'_le`, and
     `Finset.le_sup'` provide the canonical descent and finite-maximum steps.
     No library theorem packages this weighted observation quotient. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.MetricGeometryLaws.WeightedObservationQuotientUltrametric

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.Observer.MetricGeometry.DiscretePredictionUltrametric
open D5.S3.Observer.MetricGeometryLaws.WeightedPredictionZeroKernel

/-- The canonical descent of the weighted coordinate distance to the kernel
quotient of the selected joint readout. -/
noncomputable def weightedObservationQuotientDistance
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i) :
    Quotient (Setoid.ker (jointReadout (fun i : J => readout i.1))) ->
      Quotient (Setoid.ker (jointReadout (fun i : J => readout i.1))) -> Real :=
  fun first second =>
    Quotient.liftOn₂ first second
      (weightedCoordinateDistance J weight readout) (by
        classical
        intro x y x' y' hx hy
        change jointReadout (fun i : J => readout i.1) x =
          jointReadout (fun i : J => readout i.1) x' at hx
        change jointReadout (fun i : J => readout i.1) y =
          jointReadout (fun i : J => readout i.1) y' at hy
        by_cases hJ : J.Nonempty
        · simp only [weightedCoordinateDistance, dif_pos hJ]
          refine Finset.sup'_congr hJ rfl ?_
          intro i hi
          have hxCoordinate : readout i x = readout i x' := by
            simpa [jointReadout] using congrFun hx ⟨i, hi⟩
          have hyCoordinate : readout i y = readout i y' := by
            simpa [jointReadout] using congrFun hy ⟨i, hi⟩
          rw [hxCoordinate, hyCoordinate]
        · simp [weightedCoordinateDistance, hJ])

private theorem weighted_coordinate_distance_nonnegative
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (hpositive : forall i, i ∈ J -> 0 < weight i) (x y : X) :
    0 <= weightedCoordinateDistance J weight readout x y := by
  classical
  by_cases hJ : J.Nonempty
  · simp only [weightedCoordinateDistance, dif_pos hJ]
    obtain ⟨i, hi⟩ := hJ
    have termNonnegative :
        0 <= weight i *
          @discreteOutputDistance (O i) (Classical.decEq (O i))
            (readout i x) (readout i y) := by
      by_cases equal : readout i x = readout i y
      · simp [discreteOutputDistance, equal]
      · simpa [discreteOutputDistance, equal] using (hpositive i hi).le
    exact termNonnegative.trans
      (Finset.le_sup' (s := J) (f := fun j =>
        weight j * @discreteOutputDistance (O j) (Classical.decEq (O j))
          (readout j x) (readout j y)) hi)
  · simp [weightedCoordinateDistance, hJ]

private theorem weighted_coordinate_distance_zero_iff_joint_readout
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (hpositive : forall i, i ∈ J -> 0 < weight i) (x y : X) :
    weightedCoordinateDistance J weight readout x y = 0 <->
      jointReadout (fun i : J => readout i.1) x =
        jointReadout (fun i : J => readout i.1) y := by
  classical
  by_cases hJ : J.Nonempty
  · constructor
    · intro zeroDistance
      funext selected
      by_contra different
      have termLeDistance :
          weight selected.1 *
              @discreteOutputDistance (O selected.1)
                (Classical.decEq (O selected.1))
                (readout selected.1 x) (readout selected.1 y) <=
            weightedCoordinateDistance J weight readout x y := by
        simp only [weightedCoordinateDistance, dif_pos hJ]
        exact Finset.le_sup' (s := J) (f := fun i =>
          weight i * @discreteOutputDistance (O i) (Classical.decEq (O i))
            (readout i x) (readout i y)) selected.2
      have termPositive :
          0 < weight selected.1 *
            @discreteOutputDistance (O selected.1)
              (Classical.decEq (O selected.1))
              (readout selected.1 x) (readout selected.1 y) := by
        have differentCoordinate :
            readout selected.1 x ≠ readout selected.1 y := by
          simpa [jointReadout] using different
        simpa [discreteOutputDistance, differentCoordinate] using
          hpositive selected.1 selected.2
      rw [zeroDistance] at termLeDistance
      exact (not_lt_of_ge termLeDistance termPositive)
    · intro sameReadout
      apply le_antisymm
      · simp only [weightedCoordinateDistance, dif_pos hJ]
        apply Finset.sup'_le
        intro i hi
        have sameCoordinate : readout i x = readout i y := by
          simpa [jointReadout] using congrFun sameReadout ⟨i, hi⟩
        simp [discreteOutputDistance, sameCoordinate]
      · exact weighted_coordinate_distance_nonnegative
          J weight readout hpositive x y
  · constructor
    · intro _
      funext selected
      exact (hJ ⟨selected.1, selected.2⟩).elim
    · intro _
      simp [weightedCoordinateDistance, hJ]

private theorem weighted_coordinate_distance_self
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (hpositive : forall i, i ∈ J -> 0 < weight i) (x : X) :
    weightedCoordinateDistance J weight readout x x = 0 :=
  (weighted_coordinate_distance_zero_iff_joint_readout
    J weight readout hpositive x x).2 rfl

private theorem weighted_coordinate_distance_symm
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (x y : X) :
    weightedCoordinateDistance J weight readout x y =
      weightedCoordinateDistance J weight readout y x := by
  classical
  by_cases hJ : J.Nonempty
  · simp only [weightedCoordinateDistance, dif_pos hJ]
    refine Finset.sup'_congr hJ rfl ?_
    intro i _
    by_cases equal : readout i x = readout i y
    · unfold discreteOutputDistance
      rw [if_pos equal, if_pos equal.symm]
    · have reverseDifferent : readout i y ≠ readout i x := by
        exact fun reverse => equal reverse.symm
      unfold discreteOutputDistance
      rw [if_neg equal, if_neg reverseDifferent]
  · simp [weightedCoordinateDistance, hJ]

private theorem weighted_coordinate_distance_strong_triangle
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (hpositive : forall i, i ∈ J -> 0 < weight i) (x y z : X) :
    weightedCoordinateDistance J weight readout x z <=
      max (weightedCoordinateDistance J weight readout x y)
        (weightedCoordinateDistance J weight readout y z) := by
  classical
  by_cases hJ : J.Nonempty
  · simp only [weightedCoordinateDistance, dif_pos hJ]
    apply Finset.sup'_le
    intro i hi
    have coordinateTriangle :
        @discreteOutputDistance (O i) (Classical.decEq (O i))
            (readout i x) (readout i z) <=
          max
            (@discreteOutputDistance (O i) (Classical.decEq (O i))
              (readout i x) (readout i y))
            (@discreteOutputDistance (O i) (Classical.decEq (O i))
              (readout i y) (readout i z)) := by
      by_cases xz : readout i x = readout i z
      · have leftZero :
            @discreteOutputDistance (O i) (Classical.decEq (O i))
                (readout i x) (readout i z) = 0 := by
            simp [discreteOutputDistance, xz]
        rw [leftZero]
        apply le_trans ?_ (le_max_left _ _)
        by_cases xy : readout i x = readout i y
        · simp [discreteOutputDistance, xy]
        · simp [discreteOutputDistance, xy]
      by_cases xy : readout i x = readout i y
      · have yz : readout i y ≠ readout i z := by
          intro same
          exact xz (xy.trans same)
        simp [discreteOutputDistance, xy, yz]
      · simp [discreteOutputDistance, xz, xy]
    calc
      weight i * @discreteOutputDistance (O i) (Classical.decEq (O i))
          (readout i x) (readout i z) <=
          weight i *
            max
              (@discreteOutputDistance (O i) (Classical.decEq (O i))
                (readout i x) (readout i y))
              (@discreteOutputDistance (O i) (Classical.decEq (O i))
                (readout i y) (readout i z)) :=
        mul_le_mul_of_nonneg_left coordinateTriangle (hpositive i hi).le
      _ = max
          (weight i * @discreteOutputDistance (O i) (Classical.decEq (O i))
            (readout i x) (readout i y))
          (weight i * @discreteOutputDistance (O i) (Classical.decEq (O i))
            (readout i y) (readout i z)) := by
        rw [mul_max_of_nonneg _ _ (hpositive i hi).le]
      _ <= max
          (J.sup' hJ (fun j =>
            weight j * @discreteOutputDistance (O j) (Classical.decEq (O j))
              (readout j x) (readout j y)))
          (J.sup' hJ (fun j =>
            weight j * @discreteOutputDistance (O j) (Classical.decEq (O j))
              (readout j y) (readout j z))) := by
        exact max_le_max
          (Finset.le_sup' (s := J) (f := fun j =>
            weight j * @discreteOutputDistance (O j) (Classical.decEq (O j))
              (readout j x) (readout j y)) hi)
          (Finset.le_sup' (s := J) (f := fun j =>
            weight j * @discreteOutputDistance (O j) (Classical.decEq (O j))
              (readout j y) (readout j z)) hi)
  · simp [weightedCoordinateDistance, hJ]

/-- Positive coordinate weights make zero source distance exactly equality of
the selected joint readout. The canonical quotient lift computes to that
source distance and satisfies every genuine ultrametric law. -/
theorem weighted_observation_zero_kernel_and_quotient_ultrametric
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (hpositive : forall i, i ∈ J -> 0 < weight i) :
    (forall x y,
      weightedCoordinateDistance J weight readout x y = 0 <->
        jointReadout (fun i : J => readout i.1) x =
          jointReadout (fun i : J => readout i.1) y) /\
    (forall x y,
      weightedObservationQuotientDistance J weight readout
          (Quotient.mk _ x) (Quotient.mk _ y) =
        weightedCoordinateDistance J weight readout x y) /\
    (forall first second,
      0 <= weightedObservationQuotientDistance J weight readout first second) /\
    (forall point,
      weightedObservationQuotientDistance J weight readout point point = 0) /\
    (forall first second,
      weightedObservationQuotientDistance J weight readout first second =
        weightedObservationQuotientDistance J weight readout second first) /\
    (forall first second third,
      weightedObservationQuotientDistance J weight readout first third <=
        max
          (weightedObservationQuotientDistance J weight readout first second)
          (weightedObservationQuotientDistance J weight readout second third)) /\
    (forall first second,
      weightedObservationQuotientDistance J weight readout first second = 0 <->
        first = second) := by
  refine ⟨weighted_coordinate_distance_zero_iff_joint_readout
      J weight readout hpositive, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    rfl
  · intro first second
    refine Quotient.inductionOn₂ first second ?_
    intro x y
    exact weighted_coordinate_distance_nonnegative
      J weight readout hpositive x y
  · intro point
    refine Quotient.inductionOn point ?_
    intro x
    exact weighted_coordinate_distance_self J weight readout hpositive x
  · intro first second
    refine Quotient.inductionOn₂ first second ?_
    intro x y
    exact weighted_coordinate_distance_symm J weight readout x y
  · intro first second third
    refine Quotient.inductionOn first ?_
    intro x
    refine Quotient.inductionOn second ?_
    intro y
    refine Quotient.inductionOn third ?_
    intro z
    exact weighted_coordinate_distance_strong_triangle
      J weight readout hpositive x y z
  · intro first second
    refine Quotient.inductionOn₂ first second ?_
    intro x y
    constructor
    · intro zeroDistance
      apply Quotient.sound
      exact (weighted_coordinate_distance_zero_iff_joint_readout
        J weight readout hpositive x y).1 zeroDistance
    · intro sameClass
      apply (weighted_coordinate_distance_zero_iff_joint_readout
        J weight readout hpositive x y).2
      exact Quotient.exact sameClass

example :
    ∀ i ∈ ({()} : Finset Unit),
      0 < (fun _ : Unit => (1 : Real)) i := by
  simp

example :
    Nonempty
      (Quotient
        (Setoid.ker
          (jointReadout
            (fun _ : ({()} : Finset Unit) => fun x : Bool => x)))) :=
  ⟨Quotient.mk _ false⟩

#print axioms weightedObservationQuotientDistance
#print axioms weighted_observation_zero_kernel_and_quotient_ultrametric

end D5.S3.Observer.MetricGeometryLaws.WeightedObservationQuotientUltrametric
