/- GID: D5/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/ModelRelativeCompletenessDifferenceCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Model completeness is a zero-intersection criterion; empty models need care. -/

import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Ring.Int.Defs
import D5.S3.ConceptDynamics.Faithfulness.LocalGlobalResidualCriterion

/- Library-search audit trail (2026-08-25):
   * Repository searches by model-relative completeness, difference kernels,
     `Set.InjOn`, digest, generalized shape, and alternate identification
     vocabulary found no equivalent theorem. The imported local-global theorem
     supplies the residual-emptiness/injectivity half rather than being rebuilt.
   * LeanSearch for injectivity on a subset versus a kernel/difference-set
     intersection returned no API response. Loogle for `x - y = 0 <-> x = y`
     found the exact pinned-Mathlib theorem `sub_eq_zero`.
   * Local pinned-Mathlib search found `Set.injOn_iff_injective`,
     `LinearMap.sub_mem_ker_iff`, and `LinearMap.disjoint_ker_iff_injOn`.
     The linear-map results require a submodule, so they do not cover an
     arbitrary prior model set; `map_sub`, `map_zero`, and `sub_eq_zero` are
     used below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.ModelRelativeCompletenessDifferenceCriterion

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.Faithfulness.LocalGlobalResidualCriterion

universe u v w

/-- A readout family is complete relative to a model when its joint readout is
injective after restricting the state type to that model. -/
def modelRelativeComplete {I : Type u} {X : Type v} {V : I -> Type w}
    (readout : forall i, X -> V i) (model : Set X) : Prop :=
  Function.Injective
    (jointReadout (fun i (state : model) => readout i state.1))

/-- The difference set of a model consists of all ordered state differences. -/
def modelDifference {X : Type v} [Sub X] (model : Set X) : Set X :=
  {difference | ∃ left, left ∈ model ∧ ∃ right, right ∈ model ∧
    difference = left - right}

/-- The additive form of the joint residual consists of differences that the
joint kernel cannot distinguish from zero. -/
def jointDifferenceResidual {I : Type u} {X : Type v} {V : I -> Type w}
    [Zero X] (readout : forall i, X -> V i) : Set X :=
  {difference | (difference, 0) ∈ jointKernel readout}

/-- On a nonempty prior model, completeness is equivalent to the observer's
additive joint residual meeting the model difference set only at zero. -/
theorem model_relative_completeness_difference_criterion
    {I : Type u} {X : Type v} {V : I -> Type w}
    [AddGroup X] [forall i, AddGroup (V i)]
    (q : forall i, AddMonoidHom X (V i)) (model : Set X)
    (modelNonempty : model.Nonempty) :
    modelRelativeComplete (fun i state => q i state) model <->
      jointDifferenceResidual (fun i state => q i state) ∩
        modelDifference model = {0} := by
  constructor
  · intro complete
    unfold modelRelativeComplete at complete
    apply Set.Subset.antisymm
    · rintro difference ⟨inResidual, inDifference⟩
      rcases inDifference with
        ⟨left, leftInModel, right, rightInModel, rfl⟩
      have equalReadings : forall i, q i left = q i right := by
        intro i
        have hKernel := inResidual
        simp only [jointDifferenceResidual, jointKernel, conceptKernel,
          Set.mem_setOf_eq, Set.mem_iInter] at hKernel
        have hi := hKernel i
        rw [map_sub, map_zero, sub_eq_zero] at hi
        exact hi
      have equalStates :
          (⟨left, leftInModel⟩ : model) = ⟨right, rightInModel⟩ := by
        apply complete
        funext i
        exact equalReadings i
      exact Set.mem_singleton_iff.mpr
        (sub_eq_zero.mpr (congrArg Subtype.val equalStates))
    · intro difference inSingleton
      have differenceZero : difference = 0 :=
        Set.mem_singleton_iff.mp inSingleton
      subst difference
      refine ⟨?_, ?_⟩
      · simp [jointDifferenceResidual, jointKernel, conceptKernel]
      · rcases modelNonempty with ⟨state, stateInModel⟩
        exact ⟨state, stateInModel, state, stateInModel,
          (sub_self state).symm⟩
  · intro intersectionCriterion
    unfold modelRelativeComplete
    apply (local_global_residual_empty_iff_joint_injective
      (fun i (state : model) => q i state.1)).mp
    refine IsEmpty.mk fun collision => ?_
    have inResidual :
        collision.1.1.1 - collision.1.2.1 ∈
          jointDifferenceResidual (fun i state => q i state) := by
      simp only [jointDifferenceResidual, jointKernel, conceptKernel,
        Set.mem_setOf_eq, Set.mem_iInter]
      intro i
      rw [map_sub, map_zero, sub_eq_zero]
      exact collision.property.2 i
    have inDifference :
        collision.1.1.1 - collision.1.2.1 ∈ modelDifference model :=
      ⟨collision.1.1.1, collision.1.1.2,
        collision.1.2.1, collision.1.2.2, rfl⟩
    have inSingleton :
        collision.1.1.1 - collision.1.2.1 ∈ ({0} : Set X) := by
      rw [← intersectionCriterion]
      exact ⟨inResidual, inDifference⟩
    apply collision.property.1
    apply Subtype.ext
    exact sub_eq_zero.mp (Set.mem_singleton_iff.mp inSingleton)

#print axioms model_relative_completeness_difference_criterion

/-- The nonempty-model premise is necessary for the equality with `{0}`:
the empty integer model is vacuously complete, but has no differences. -/
theorem model_nonempty_is_necessary :
    let q : forall _ : Unit, AddMonoidHom Int Int :=
      fun _ => AddMonoidHom.id Int
    modelRelativeComplete (fun i state => q i state) (∅ : Set Int) ∧
      jointDifferenceResidual (fun i state => q i state) ∩
        modelDifference (∅ : Set Int) ≠ {0} := by
  dsimp only
  constructor
  · unfold modelRelativeComplete
    intro left _ _
    exact left.property.elim
  · simp [modelDifference]

#print axioms model_nonempty_is_necessary

/-- Additivity is necessary to turn equal readings into a zero reading of a
difference: squaring identifies `-1` and `1`, although neither difference `2`
nor `-2` lies in its zero residual. -/
theorem additivity_is_necessary :
    let readout : forall _ : Unit, Int -> Int := fun _ state => state * state
    let model : Set Int := {-1, 1}
    ¬modelRelativeComplete readout model ∧
      jointDifferenceResidual readout ∩ modelDifference model = {0} := by
  dsimp only
  constructor
  · intro complete
    unfold modelRelativeComplete at complete
    have equalStates :
        (⟨-1, by simp⟩ : ({-1, 1} : Set Int)) = ⟨1, by simp⟩ := by
      apply complete
      funext i
      rcases i with ⟨⟩
      rfl
    have impossible := congrArg Subtype.val equalStates
    simp at impossible
  · have residualEq :
        jointDifferenceResidual
            (fun _ : Unit => fun state : Int => state * state) = {0} := by
      ext difference
      simp [jointDifferenceResidual, jointKernel, conceptKernel]
    rw [residualEq, Set.inter_eq_left]
    rw [Set.singleton_subset_iff]
    exact ⟨-1, by simp, -1, by simp, (sub_self (-1 : Int)).symm⟩

#print axioms additivity_is_necessary

/-- Degenerate audit: an additive carrier cannot be empty because it contains zero. -/
theorem additive_carrier_is_nonempty {X : Type*} [AddGroup X] : Nonempty X :=
  ⟨0⟩

#print axioms additive_carrier_is_nonempty

/-- Degenerate audit: every readout is complete on the one-element state type. -/
theorem unit_model_is_complete :
    modelRelativeComplete (fun _ : Unit => fun _ : Unit => ()) Set.univ := by
  unfold modelRelativeComplete
  intro left right _
  exact Subtype.ext (Subsingleton.elim left.1 right.1)

#print axioms unit_model_is_complete

/-- Degenerate audit: with no coordinates, a singleton prior remains complete. -/
theorem empty_coordinate_singleton_model_is_complete :
    modelRelativeComplete
      ((fun index : Empty => index.elim) : forall _ : Empty, Int -> Unit)
      ({0} : Set Int) := by
  unfold modelRelativeComplete
  intro left right _
  apply Subtype.ext
  simpa using left.property.trans right.property.symm

#print axioms empty_coordinate_singleton_model_is_complete

/-- Degenerate audit: a constant readout is incomplete on a nontrivial state type. -/
theorem constant_readout_is_incomplete :
    ¬modelRelativeComplete
      (fun _ : Unit => fun _ : Bool => ()) (Set.univ : Set Bool) := by
  intro complete
  unfold modelRelativeComplete at complete
  have equalStates :
      (⟨false, Set.mem_univ false⟩ : (Set.univ : Set Bool)) =
        ⟨true, Set.mem_univ true⟩ := by
    apply complete
    rfl
  exact Bool.false_ne_true (congrArg Subtype.val equalStates)

#print axioms constant_readout_is_incomplete

/-- Degenerate audit: an identity coordinate is complete on every prior model. -/
theorem identity_readout_is_complete_on_every_model
    {X : Type*} (model : Set X) :
    modelRelativeComplete (fun _ : Unit => (id : X -> X)) model := by
  unfold modelRelativeComplete
  intro left right equalReadings
  apply Subtype.ext
  exact congrFun equalReadings ()

#print axioms identity_readout_is_complete_on_every_model

end D5.S3.ConceptDynamics.Faithfulness.ModelRelativeCompletenessDifferenceCriterion
