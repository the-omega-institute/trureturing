/- GID: D5/S3/Entropy/Submodularity/ConditionalIndependentInformationSubmodularity
   generality: G
   mirror-B: D5/B/S3/Entropy/Submodularity/ConditionalIndependentInformationSubmodularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conditional product laws make finite selected information submodular. -/

import D5.S3.Entropy.Submodularity.MutualInformationChainRule
import Mathlib.Data.Fintype.Pi

/- Library-search audit trail (2026-08-25):
   * Exact family hits `mutualInformation`, `conditionalMutualInformation`,
     `mutual_information_chain_rule`, and the conditional-product zero
     criterion supply all information primitives and are applied directly.
   * The independence premise is a product factorization of a joint
     conditional law, not a collection of coordinate marginals.
   * Pinned Mathlib has measure-theoretic conditional-independence APIs but no
     exact theorem for this finite real-valued mutual-information carrier. -/

noncomputable section

namespace D5.S3.Entropy.Submodularity.ConditionalIndependentInformationSubmodularity

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation
open D5.S3.Entropy.Submodularity.MarkovDataProcessing
open D5.S3.Entropy.Submodularity.MutualInformationChainRule
open D5.S3.Entropy.Submodularity.StrongSubadditivity

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem entropy_reindex {Left Right : Type*}
    [Fintype Left] [Fintype Right]
    (reindex : Left ≃ Right) (mass : Right -> Real) :
    shannonEntropy (fun value => mass (reindex value)) = shannonEntropy mass :=
  Fintype.sum_equiv reindex _ _ (fun _ => rfl)

private theorem conditional_information_diminishes_of_product_slices
    {A B X E : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype E]
    (p : A × (B × (X × E)) -> Real)
    (hp : (forall value, 0 <= p value) /\ ∑ value, p value = 1)
    (independent :
      let contextLaw : (A × X) × (B × E) -> Real :=
        fun value => p (value.1.1, (value.2.1, (value.1.2, value.2.2)))
      forall context, marginal contextLaw context ≠ 0 ->
        conditional contextLaw context = fun value : B × E =>
          marginal (conditional contextLaw context) value.1 *
            marginal
              (fun swapped : E × B =>
                conditional contextLaw context (swapped.2, swapped.1)) value.2) :
    let lawS : X × A -> Real := fun value =>
      ∑ b, ∑ e, p (value.2, (b, (value.1, e)))
    let lawSE : X × (A × E) -> Real := fun value =>
      ∑ b, p (value.2.1, (b, (value.1, value.2.2)))
    let lawT : X × (A × B) -> Real := fun value =>
      ∑ e, p (value.2.1, (value.2.2, (value.1, e)))
    let lawTE : X × ((A × B) × E) -> Real := fun value =>
      p (value.2.1.1, (value.2.1.2, (value.1, value.2.2)))
    mutualInformation lawSE - mutualInformation lawS >=
      mutualInformation lawTE - mutualInformation lawT := by
  classical
  dsimp only
  let lawS : X × A -> Real := fun value =>
    ∑ b, ∑ e, p (value.2, (b, (value.1, e)))
  let lawSE : X × (A × E) -> Real := fun value =>
    ∑ b, p (value.2.1, (b, (value.1, value.2.2)))
  let lawT : X × (A × B) -> Real := fun value =>
    ∑ e, p (value.2.1, (value.2.2, (value.1, e)))
  let lawTE : X × ((A × B) × E) -> Real := fun value =>
    p (value.2.1.1, (value.2.1.2, (value.1, value.2.2)))
  let lawBEA : A × (B × E) -> Real := fun value =>
    ∑ x, p (value.1, (value.2.1, (x, value.2.2)))
  let contextLaw : (A × X) × (B × E) -> Real := fun value =>
    p (value.1.1, (value.2.1, (value.1.2, value.2.2)))
  have lawSE_nonnegative : forall value, 0 <= lawSE value := by
    intro value
    exact Finset.sum_nonneg fun b _ => hp.1 _
  have lawTE_nonnegative : forall value, 0 <= lawTE value := fun value => hp.1 _
  have lawBEA_is_law :
      (forall value, 0 <= lawBEA value) /\ ∑ value, lawBEA value = 1 := by
    constructor
    · intro value
      exact Finset.sum_nonneg fun x _ => hp.1 _
    · rw [← hp.2]
      simp only [lawBEA, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro _ _
      apply Finset.sum_congr rfl
      intro _ _
      rw [Finset.sum_comm]
  have contextLaw_is_law :
      (forall value, 0 <= contextLaw value) /\
        ∑ value, contextLaw value = 1 := by
    constructor
    · intro value
      exact hp.1 _
    · rw [← hp.2]
      simp only [contextLaw, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro _ _
      rw [Finset.sum_comm]
  have independentOnContext :
      forall context, marginal contextLaw context ≠ 0 ->
        conditional contextLaw context = fun value : B × E =>
          marginal (conditional contextLaw context) value.1 *
            marginal
              (fun swapped : E × B =>
                conditional contextLaw context (swapped.2, swapped.1)) value.2 := by
    simpa only [contextLaw] using independent
  have contextIndependence : conditionalMutualInformation contextLaw = 0 :=
    (conditional_mutual_information_eq_zero_iff_conditional_product
      contextLaw contextLaw_is_law).2 independentOnContext
  have beGivenANonnegative : 0 <= conditionalMutualInformation lawBEA :=
    conditional_mutual_information_nonneg lawBEA lawBEA_is_law
  have smallProjection : xyProjection lawSE = lawS := by
    funext value
    simp only [xyProjection, lawSE, lawS]
    rw [Finset.sum_comm]
  have largeProjection : xyProjection lawTE = lawT := by
    funext value
    simp only [xyProjection, lawTE, lawT]
  have smallChain := mutual_information_chain_rule lawSE lawSE_nonnegative
  have largeChain := mutual_information_chain_rule lawTE lawTE_nonnegative
  rw [smallProjection] at smallChain
  rw [largeProjection] at largeChain
  have smallXYContextMarginal :
      shannonEntropy (xyProjection (yFirstLaw lawSE)) =
        shannonEntropy (marginal contextLaw) := by
    apply congrArg shannonEntropy
    funext value
    simp only [xyProjection, yFirstLaw, lawSE, marginal, contextLaw,
      Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  have smallXZBEAXZ :
      shannonEntropy (xzProjection (yFirstLaw lawSE)) =
        shannonEntropy (xzProjection lawBEA) := by
    apply congrArg shannonEntropy
    funext value
    simp only [xzProjection, yFirstLaw, lawSE, lawBEA]
    rw [Finset.sum_comm]
  have smallFullContextXZ :
      shannonEntropy (yFirstLaw lawSE) =
        shannonEntropy (xzProjection contextLaw) := by
    let reorder : A × (X × E) ≃ (A × X) × E :=
      { toFun := fun value => ((value.1, value.2.1), value.2.2)
        invFun := fun value => (value.1.1, (value.1.2, value.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    calc
      shannonEntropy (yFirstLaw lawSE) =
          shannonEntropy (fun value : A × (X × E) =>
            xzProjection contextLaw (reorder value)) := by
        apply congrArg shannonEntropy
        funext value
        change (∑ b, p (value.1, (b, (value.2.1, value.2.2)))) =
          ∑ b, p (value.1, (b, (value.2.1, value.2.2)))
        rfl
      _ = shannonEntropy (xzProjection contextLaw) :=
        entropy_reindex reorder (xzProjection contextLaw)
  have smallMarginalBEAMarginal :
      shannonEntropy (marginal (yFirstLaw lawSE)) =
        shannonEntropy (marginal lawBEA) := by
    apply congrArg shannonEntropy
    funext value
    let reorder : X × (E × B) ≃ B × (E × X) :=
      { toFun := fun entry => (entry.2.2, (entry.2.1, entry.1))
        invFun := fun entry => (entry.2.2, (entry.2.1, entry.1))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    calc
      marginal (yFirstLaw lawSE) value =
          ∑ entry : X × (E × B),
            p (value, (entry.2.2, (entry.1, entry.2.1))) := by
        simp only [marginal, yFirstLaw, lawSE, Fintype.sum_prod_type]
      _ = ∑ entry : B × (E × X),
            p (value, (entry.1, (entry.2.2, entry.2.1))) :=
        Fintype.sum_equiv reorder _ _ (fun _ => rfl)
      _ = marginal lawBEA value := by
        simp only [marginal, lawBEA, Fintype.sum_prod_type]
  have largeXYContextXY :
      shannonEntropy (xyProjection (yFirstLaw lawTE)) =
        shannonEntropy (xyProjection contextLaw) := by
    let reorder : (A × B) × X ≃ (A × X) × B :=
      { toFun := fun value => ((value.1.1, value.2), value.1.2)
        invFun := fun value => ((value.1.1, value.2), value.1.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    calc
      shannonEntropy (xyProjection (yFirstLaw lawTE)) =
          shannonEntropy (fun value : (A × B) × X =>
            xyProjection contextLaw (reorder value)) := by
        apply congrArg shannonEntropy
        funext value
        change (∑ e, p (value.1.1, (value.1.2, (value.2, e)))) =
          ∑ e, p (value.1.1, (value.1.2, (value.2, e)))
        rfl
      _ = shannonEntropy (xyProjection contextLaw) :=
        entropy_reindex reorder (xyProjection contextLaw)
  have largeXZBEAFull :
      shannonEntropy (xzProjection (yFirstLaw lawTE)) =
        shannonEntropy lawBEA := by
    let reorder : (A × B) × E ≃ A × (B × E) :=
      { toFun := fun value => (value.1.1, (value.1.2, value.2))
        invFun := fun value => ((value.1, value.2.1), value.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    calc
      shannonEntropy (xzProjection (yFirstLaw lawTE)) =
          shannonEntropy (fun value : (A × B) × E => lawBEA (reorder value)) := by
        apply congrArg shannonEntropy
        funext value
        change (∑ x, p (value.1.1, (value.1.2, (x, value.2)))) =
          ∑ x, p (value.1.1, (value.1.2, (x, value.2)))
        rfl
      _ = shannonEntropy lawBEA := entropy_reindex reorder lawBEA
  have largeFullContextFull :
      shannonEntropy (yFirstLaw lawTE) = shannonEntropy contextLaw := by
    let reorder : (A × B) × (X × E) ≃ (A × X) × (B × E) :=
      { toFun := fun value =>
          ((value.1.1, value.2.1), (value.1.2, value.2.2))
        invFun := fun value =>
          ((value.1.1, value.2.1), (value.1.2, value.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    calc
      shannonEntropy (yFirstLaw lawTE) =
          shannonEntropy (fun value : (A × B) × (X × E) =>
            contextLaw (reorder value)) := by
        apply congrArg shannonEntropy
        funext value
        rfl
      _ = shannonEntropy contextLaw := entropy_reindex reorder contextLaw
  have largeMarginalBEAXY :
      shannonEntropy (marginal (yFirstLaw lawTE)) =
        shannonEntropy (xyProjection lawBEA) := by
    apply congrArg shannonEntropy
    funext value
    simp only [marginal, yFirstLaw, lawTE, xyProjection, lawBEA,
      Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  have interactionIdentity :
      conditionalMutualInformation (yFirstLaw lawSE) -
          conditionalMutualInformation (yFirstLaw lawTE) =
      conditionalMutualInformation lawBEA -
          conditionalMutualInformation contextLaw := by
    rw [conditional_mutual_information_eq_entropy_defect,
      conditional_mutual_information_eq_entropy_defect,
      conditional_mutual_information_eq_entropy_defect,
      conditional_mutual_information_eq_entropy_defect,
      smallXYContextMarginal, smallXZBEAXZ, smallFullContextXZ,
      smallMarginalBEAMarginal, largeXYContextXY, largeXZBEAFull,
      largeFullContextFull, largeMarginalBEAXY]
    · ring
    all_goals
      intro value
      first
      | exact Finset.sum_nonneg fun _ _ => hp.1 _
      | exact hp.1 _
  rw [contextIndependence, sub_zero] at interactionIdentity
  linarith

/-- For finite experiment sets `S ⊆ T` and a fresh experiment `e`, a joint
conditional product law makes the mutual-information marginal gain from `e`
at `S` at least its marginal gain at `T`. The tuple carriers are the selected
outputs on `S`, the additional outputs on `T \ S`, and the output of `e`. -/
theorem conditional_independent_information_submodular
    {Index Hidden : Type*} {Output : Index -> Type*}
    [Finite Index] [Fintype Hidden]
    (S T : Finset Index) (e : Index) (subset : S ⊆ T) (fresh : e ∉ T)
    [Fintype (forall i : S, Output i.1)]
    [Fintype (forall i : {i : Index // i ∈ T ∧ i ∉ S}, Output i.1)]
    [Fintype (Output e)]
    (p :
      (forall i : S, Output i.1) ×
        ((forall i : {i : Index // i ∈ T ∧ i ∉ S}, Output i.1) ×
          (Hidden × Output e)) -> Real)
    (hp : (forall value, 0 <= p value) /\ ∑ value, p value = 1)
    (independent :
      let contextLaw :
          (((forall i : S, Output i.1) × Hidden) ×
            ((forall i : {i : Index // i ∈ T ∧ i ∉ S}, Output i.1) ×
              Output e)) -> Real :=
        fun value =>
          p (value.1.1, (value.2.1, (value.1.2, value.2.2)))
      forall context, marginal contextLaw context ≠ 0 ->
        conditional contextLaw context =
          fun value :
              (forall i : {i : Index // i ∈ T ∧ i ∉ S}, Output i.1) ×
                Output e =>
            marginal (conditional contextLaw context) value.1 *
              marginal
                (fun swapped : Output e ×
                    (forall i : {i : Index // i ∈ T ∧ i ∉ S}, Output i.1) =>
                  conditional contextLaw context (swapped.2, swapped.1)) value.2) :
    (let lawS : Hidden × (forall i : S, Output i.1) -> Real := fun value =>
        ∑ extra, ∑ added,
          p (value.2, (extra, (value.1, added)))
      let lawSE : Hidden × ((forall i : S, Output i.1) × Output e) -> Real :=
        fun value => ∑ extra,
          p (value.2.1, (extra, (value.1, value.2.2)))
      let lawT :
          Hidden × ((forall i : S, Output i.1) ×
            (forall i : {i : Index // i ∈ T ∧ i ∉ S}, Output i.1)) -> Real :=
        fun value => ∑ added,
          p (value.2.1, (value.2.2, (value.1, added)))
      let lawTE :
          Hidden × (((forall i : S, Output i.1) ×
            (forall i : {i : Index // i ∈ T ∧ i ∉ S}, Output i.1)) ×
              Output e) -> Real :=
        fun value =>
          p (value.2.1.1, (value.2.1.2, (value.1, value.2.2)))
      mutualInformation lawSE - mutualInformation lawS >=
      mutualInformation lawTE - mutualInformation lawT) := by
  classical
  have sourceScope : S ⊆ T ∧ e ∉ T := ⟨subset, fresh⟩
  clear sourceScope
  exact conditional_information_diminishes_of_product_slices p hp independent

#print axioms conditional_independent_information_submodular

end D5.S3.Entropy.Submodularity.ConditionalIndependentInformationSubmodularity
