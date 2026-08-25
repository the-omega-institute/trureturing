/- GID: D5/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometryLaws/WeightedJointUltrapseudometric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint laws descend and separate, including empty budgets and index types. -/

/- Library-search audit trail (2026-08-25):
   * Repository search found and reuses `WeightedPredictionZeroKernel.weightedCoordinateDistance`;
     its three supporting coordinate lemmas are private and therefore cannot cover these atoms.
   * Repository search found and reuses the canonical dependent product `jointReadout`; the
     selected joint readout below is only its finite-budget specialization.
   * Loogle exact-name searches hit `Finset.sup'_le` and `Finset.le_sup'`; both are applied.
     Pinned Mathlib also supplies `Finset.sup'_eq_of_forall`, `Finset.sup'_congr`,
     `mul_max_of_nonneg`, `Setoid.ker`, `Quotient.liftOn₂`, and `Quotient.sound`.
   * Exact repository searches found no public weighted joint strong triangle, static zero
     kernel, sign counterexamples, or quotient descent theorem. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import D5.S3.Observer.MetricGeometryLaws.WeightedPredictionZeroKernel
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.MetricGeometryLaws.WeightedJointUltrapseudometric

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.Observer.MetricGeometry.DiscretePredictionUltrametric
open D5.S3.Observer.MetricGeometryLaws.WeightedPredictionZeroKernel

/-- The source's joint observation `q_J`, specialized from the canonical dependent product. -/
def selectedJointReadout
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (readout : forall i, X -> O i) :
    X -> forall i : {i // i ∈ J}, O i.1 :=
  jointReadout (fun i : {i // i ∈ J} => readout i.1)

/-- Equality of the selected joint readout is the observation-kernel relation. -/
def jointObservationSetoid
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (readout : forall i, X -> O i) : Setoid X :=
  Setoid.ker (selectedJointReadout J readout)

/-- The observation quotient induced by equality of the selected joint readout. -/
def JointObservationQuotient
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (readout : forall i, X -> O i) : Type _ :=
  Quotient (jointObservationSetoid J readout)

private theorem discrete_output_distance_strong_triangle
    {O : Type*} [DecidableEq O] (a b c : O) :
    discreteOutputDistance a c <=
      max (discreteOutputDistance a b) (discreteOutputDistance b c) := by
  by_cases hac : a = c
  · subst c
    have hnonnegative : 0 <= discreteOutputDistance a b := by
      by_cases hab : a = b <;> simp [discreteOutputDistance, hab]
    calc
      discreteOutputDistance a a = 0 := by simp [discreteOutputDistance]
      _ <= discreteOutputDistance a b := hnonnegative
      _ <= max (discreteOutputDistance a b) (discreteOutputDistance b a) :=
        le_max_left _ _
  by_cases hab : a = b
  · subst b
    simp [discreteOutputDistance, hac]
  · simp [discreteOutputDistance, hac, hab]

/-- The source omits nonnegative selected weights, but that assumption is necessary for its
strong triangle inequality; the public counterexample below witnesses the omission. -/
theorem weighted_joint_ultrapseudometric
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (hnonnegative : ∀ i ∈ J, 0 <= weight i) (x y z : X) :
    weightedCoordinateDistance J weight readout x z <=
      max (weightedCoordinateDistance J weight readout x y)
        (weightedCoordinateDistance J weight readout y z) := by
  classical
  by_cases hJ : J.Nonempty
  · simp only [weightedCoordinateDistance, dif_pos hJ]
    apply Finset.sup'_le
    intro i hi
    calc
      weight i *
          @discreteOutputDistance (O i) (Classical.decEq (O i))
            (readout i x) (readout i z) <=
          weight i *
            max
              (@discreteOutputDistance (O i) (Classical.decEq (O i))
                (readout i x) (readout i y))
              (@discreteOutputDistance (O i) (Classical.decEq (O i))
                (readout i y) (readout i z)) :=
        mul_le_mul_of_nonneg_left
          (@discrete_output_distance_strong_triangle
            (O i) (Classical.decEq (O i))
            (readout i x) (readout i y) (readout i z))
          (hnonnegative i hi)
      _ = max
          (weight i *
            @discreteOutputDistance (O i) (Classical.decEq (O i))
              (readout i x) (readout i y))
          (weight i *
            @discreteOutputDistance (O i) (Classical.decEq (O i))
              (readout i y) (readout i z)) :=
        mul_max_of_nonneg _ _ (hnonnegative i hi)
      _ <= max
          (J.sup' hJ fun j =>
            weight j *
              @discreteOutputDistance (O j) (Classical.decEq (O j))
                (readout j x) (readout j y))
          (J.sup' hJ fun j =>
            weight j *
              @discreteOutputDistance (O j) (Classical.decEq (O j))
                (readout j y) (readout j z)) :=
        max_le_max
          (Finset.le_sup' (f := fun j =>
            weight j *
              @discreteOutputDistance (O j) (Classical.decEq (O j))
                (readout j x) (readout j y)) hi)
          (Finset.le_sup' (f := fun j =>
            weight j *
              @discreteOutputDistance (O j) (Classical.decEq (O j))
                (readout j y) (readout j z)) hi)
  · simp [weightedCoordinateDistance, hJ]
#print axioms weighted_joint_ultrapseudometric

/-- Strict positivity is stronger than the nonnegativity used above: it makes every selected
unequal coordinate contribute a positive term. A zero-weight counterexample below shows why
nonnegativity alone is insufficient here. -/
theorem weighted_joint_zero_distance_iff
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
          weight i *
              @discreteOutputDistance (O i) (Classical.decEq (O i))
                (readout i x) (readout i y) <=
            J.sup' hJ (fun j =>
              weight j *
                @discreteOutputDistance (O j) (Classical.decEq (O j))
                  (readout j x) (readout j y)) :=
        Finset.le_sup' (f := fun j =>
          weight j *
            @discreteOutputDistance (O j) (Classical.decEq (O j))
              (readout j x) (readout j y)) hi
      have hterm :
          0 < weight i *
            @discreteOutputDistance (O i) (Classical.decEq (O i))
              (readout i x) (readout i y) := by
        simpa [discreteOutputDistance, hne] using hpositive i hi
      simp only [weightedCoordinateDistance, dif_pos hJ] at hzero
      rw [hzero] at hle
      exact (not_lt_of_ge hle hterm)
    · intro hagree
      simp only [weightedCoordinateDistance, dif_pos hJ]
      apply Finset.sup'_eq_of_forall
      intro i hi
      simp [discreteOutputDistance, hagree i hi]
  · simp [weightedCoordinateDistance, Finset.not_nonempty_iff_eq_empty.mp hJ]
#print axioms weighted_joint_zero_distance_iff

/-- A negative singleton weight makes the source strong triangle inequality read `0 <= -1`. -/
theorem nonnegative_weights_are_necessary :
    let J : Finset Unit := {()}
    let weight : Unit -> Real := fun _ => -1
    let readout : forall _ : Unit, Bool -> Bool := fun _ => id
    (∃ i ∈ J, weight i < 0) ∧
      ¬weightedCoordinateDistance J weight readout false false <=
        max (weightedCoordinateDistance J weight readout false true)
          (weightedCoordinateDistance J weight readout true false) := by
  dsimp
  constructor
  · exact ⟨(), by simp, by norm_num⟩
  · norm_num [weightedCoordinateDistance, discreteOutputDistance]
#print axioms nonnegative_weights_are_necessary

/-- A zero singleton weight hides two unequal Boolean readouts, so strict positivity cannot be
weakened to nonnegativity in the zero-kernel theorem. -/
theorem strictly_positive_weights_are_necessary :
    let J : Finset Unit := {()}
    let weight : Unit -> Real := fun _ => 0
    let readout : forall _ : Unit, Bool -> Bool := fun _ => id
    weight () = 0 ∧
      ¬(weightedCoordinateDistance J weight readout false true = 0 <->
        ∀ i ∈ J, readout i false = readout i true) := by
  norm_num [weightedCoordinateDistance, discreteOutputDistance]
#print axioms strictly_positive_weights_are_necessary

/-- The weighted distance is invariant under changing either representative without changing
its selected joint readout. No sign condition on the weights is needed for descent. -/
theorem weighted_joint_quotient_well_defined
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    {x x' y y' : X}
    (hx : ∀ i ∈ J, readout i x = readout i x')
    (hy : ∀ i ∈ J, readout i y = readout i y') :
    weightedCoordinateDistance J weight readout x y =
      weightedCoordinateDistance J weight readout x' y' := by
  classical
  by_cases hJ : J.Nonempty
  · simp only [weightedCoordinateDistance, dif_pos hJ]
    apply Finset.sup'_congr hJ rfl
    intro i hi
    rw [hx i hi, hy i hi]
  · simp [weightedCoordinateDistance, hJ]
#print axioms weighted_joint_quotient_well_defined

/-- The representative-invariant weighted distance induced on the observation quotient. -/
noncomputable def quotientWeightedJointDistance
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (first second : JointObservationQuotient J readout) : Real :=
  Quotient.liftOn₂ first second
    (weightedCoordinateDistance J weight readout) (by
      intro x y x' y' hx hy
      change selectedJointReadout J readout x =
        selectedJointReadout J readout x' at hx
      change selectedJointReadout J readout y =
        selectedJointReadout J readout y' at hy
      apply weighted_joint_quotient_well_defined J weight readout
      · intro i hi
        exact congrFun hx ⟨i, hi⟩
      · intro i hi
        exact congrFun hy ⟨i, hi⟩)

/-- With positive selected weights, zero induced distance implies equality in the observation
quotient. This records separation without installing a global mathlib `MetricSpace` instance. -/
theorem quotient_weighted_joint_zero_implies_eq
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (hpositive : ∀ i ∈ J, 0 < weight i)
    (first second : JointObservationQuotient J readout) :
    quotientWeightedJointDistance J weight readout first second = 0 ->
      first = second := by
  refine Quotient.inductionOn₂' first second ?_
  intro x y hzero
  change weightedCoordinateDistance J weight readout x y = 0 at hzero
  have hagree :=
    (weighted_joint_zero_distance_iff J weight readout hpositive x y).mp hzero
  apply Quotient.sound
  change selectedJointReadout J readout x = selectedJointReadout J readout y
  funext i
  exact hagree i.1 i.2
#print axioms quotient_weighted_joint_zero_implies_eq

/- Degeneracy audit: the index type and budget may be empty. -/
example :
    weightedCoordinateDistance
        (I := Empty) (X := Unit) (O := fun _ => Unit)
        ∅ (fun _ => 1) (fun _ _ => ()) () () = 0 := by
  simp [weightedCoordinateDistance]

/- A constant readout is invisible even on a positive singleton budget. -/
example :
    weightedCoordinateDistance ({()} : Finset Unit) (fun _ => 1)
      (fun _ (_ : Bool) => ()) false true = 0 := by
  norm_num [weightedCoordinateDistance, discreteOutputDistance]

/- The identity readout on a positive singleton budget distinguishes the two Boolean states. -/
example :
    weightedCoordinateDistance ({()} : Finset Unit) (fun _ => 1)
        (fun _ => (id : Bool -> Bool)) false true ≠ 0 := by
  norm_num [weightedCoordinateDistance, discreteOutputDistance]

/- There is no iteration parameter n; the empty-budget case is the zero-coordinate analogue. -/

end D5.S3.Observer.MetricGeometryLaws.WeightedJointUltrapseudometric
