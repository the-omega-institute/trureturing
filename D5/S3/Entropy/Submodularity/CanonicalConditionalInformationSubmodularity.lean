/- GID: D5/S3/Entropy/Submodularity/CanonicalConditionalInformationSubmodularity
   generality: G
   mirror-B: D5/B/S3/Entropy/Submodularity/CanonicalConditionalInformationSubmodularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conditional product laws make canonical selected-output information submodular. -/

import D5.S3.Entropy.Submodularity.MutualInformationChainRule
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Pi

/- Library-search audit trail (2026-08-26):
   * Exact family hits `mutualInformation`, `conditionalMutualInformation`,
     `mutual_information_chain_rule`, and the conditional-product zero
     criterion supply the finite information primitives and are reused below.
   * Body-shape searches for selected dependent tuples hit the canonical
     `jointReadout` family and the adjacent selected-information modules, but
     no current theorem states this submodularity inequality on the exact
     `forall i : selected, Output i.1` carriers.
   * Mathlib's `Equiv.piFinsetUnion`, `Finset.subtypeInsertEquivOption`, and
     `Equiv.piOptionEquivProd` give the proved dependent-product transports.
   * Pinned Mathlib has measure-theoretic conditional-independence APIs but no
     exact theorem for this finite real-valued mutual-information carrier. -/

noncomputable section

namespace D5.S3.Entropy.Submodularity.CanonicalConditionalInformationSubmodularity

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation
open D5.S3.Entropy.Submodularity.MarkovDataProcessing
open D5.S3.Entropy.Submodularity.MutualInformationChainRule
open D5.S3.Entropy.Submodularity.StrongSubadditivity

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance {alpha : Type*} : DecidableEq alpha := Classical.decEq alpha

private theorem entropy_reindex {Left Right : Type*}
    [Fintype Left] [Fintype Right]
    (reindex : Left ≃ Right) (mass : Right -> Real) :
    shannonEntropy (fun value => mass (reindex value)) = shannonEntropy mass :=
  Fintype.sum_equiv reindex _ _ (fun _ => rfl)

private theorem mutual_information_reindex_right
    {Hidden Left Right : Type*}
    [Fintype Hidden] [Fintype Left] [Fintype Right]
    (reindex : Left ≃ Right) (mass : Hidden × Right -> Real)
    (nonnegative : forall value, 0 <= mass value) :
    mutualInformation (fun value : Hidden × Left =>
      mass (value.1, reindex value.2)) = mutualInformation mass := by
  classical
  let reindexJoint : Hidden × Left ≃ Hidden × Right :=
    (Equiv.refl Hidden).prodCongr reindex
  have firstMarginal :
      marginal (fun value : Hidden × Left => mass (value.1, reindex value.2)) =
        marginal mass := by
    funext hidden
    exact Fintype.sum_equiv reindex _ _ (fun _ => rfl)
  have secondMarginalEntropy :
      shannonEntropy
          (marginal (fun value : Left × Hidden =>
            mass (value.2, reindex value.1))) =
        shannonEntropy
          (marginal (fun value : Right × Hidden => mass (value.2, value.1))) := by
    exact entropy_reindex reindex
      (marginal (fun value : Right × Hidden => mass (value.2, value.1)))
  have jointEntropy :
      shannonEntropy (fun value : Hidden × Left =>
          mass (value.1, reindex value.2)) = shannonEntropy mass := by
    exact entropy_reindex reindexJoint mass
  rw [mutual_information_eq_entropy_sub, mutual_information_eq_entropy_sub,
    firstMarginal, secondMarginalEntropy, jointEntropy]
  · exact nonnegative
  · exact fun value => nonnegative (value.1, reindex value.2)

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

/-- For `S ⊆ T` and `e ∉ T`, a conditional product law on the canonical
dependent tuple over `insert e T` gives diminishing mutual-information returns.
The four displayed laws live on the exact tuple carriers over `S`,
`insert e S`, `T`, and `insert e T`; product splitting is used only through the
proved equivalences in the construction and proof. -/
theorem canonical_conditional_information_submodular
    {Index Hidden : Type*} {Output : Index -> Type*}
    [Fintype Hidden] [forall i, Fintype (Output i)]
    (S T : Finset Index) (e : Index) (subset : S ⊆ T) (fresh : e ∉ T)
    (p : Hidden × (forall i : (insert e T : Finset Index), Output i.1) -> Real)
    (hp : (forall value, 0 <= p value) /\ ∑ value, p value = 1) :
    let difference : Finset Index := T \ S
    let joinT :
        ((forall i : S, Output i.1) ×
          (forall i : difference, Output i.1)) ≃
            (forall i : T, Output i.1) := by
      let raw := Equiv.piFinsetUnion Output
        (Finset.disjoint_sdiff : Disjoint S (T \ S))
      rw [Finset.union_sdiff_of_subset subset] at raw
      exact raw
    let freshS : e ∉ S := fun member => fresh (subset member)
    let insertIndexT := Finset.subtypeInsertEquivOption fresh
    let reindexAddedT := insertIndexT.piCongrLeft'
      (fun i : (insert e T : Finset Index) => Output i.1)
    let splitAddedT := reindexAddedT.trans
      (Equiv.piOptionEquivProd
        (β := fun option : Option T => Output (insertIndexT.symm option).1))
    let joinAddedT :
        ((forall i : T, Output i.1) × Output e) ≃
          (forall i : (insert e T : Finset Index), Output i.1) :=
      (Equiv.prodComm _ _).trans splitAddedT.symm
    let insertIndexS := Finset.subtypeInsertEquivOption freshS
    let reindexAddedS := insertIndexS.piCongrLeft'
      (fun i : (insert e S : Finset Index) => Output i.1)
    let splitAddedS := reindexAddedS.trans
      (Equiv.piOptionEquivProd
        (β := fun option : Option S => Output (insertIndexS.symm option).1))
    let joinAddedS :
        ((forall i : S, Output i.1) × Output e) ≃
          (forall i : (insert e S : Finset Index), Output i.1) :=
      (Equiv.prodComm _ _).trans splitAddedS.symm
    let contextLaw :
        (((forall i : S, Output i.1) × Hidden) ×
          ((forall i : difference, Output i.1) × Output e)) -> Real :=
      fun value =>
        p (value.1.2,
          joinAddedT (joinT (value.1.1, value.2.1), value.2.2))
    let lawS : Hidden × (forall i : S, Output i.1) -> Real := fun value =>
      ∑ extra, ∑ added,
        p (value.1, joinAddedT (joinT (value.2, extra), added))
    let lawSE :
        Hidden × (forall i : (insert e S : Finset Index), Output i.1) -> Real :=
      fun value =>
        let separated := joinAddedS.symm value.2
        ∑ extra,
          p (value.1,
            joinAddedT (joinT (separated.1, extra), separated.2))
    let lawT : Hidden × (forall i : T, Output i.1) -> Real := fun value =>
      ∑ added, p (value.1, joinAddedT (value.2, added))
    (forall context, marginal contextLaw context ≠ 0 ->
      conditional contextLaw context =
        fun value : (forall i : difference, Output i.1) × Output e =>
          marginal (conditional contextLaw context) value.1 *
            marginal
              (fun swapped : Output e ×
                  (forall i : difference, Output i.1) =>
                conditional contextLaw context (swapped.2, swapped.1)) value.2) ->
      mutualInformation lawSE - mutualInformation lawS >=
        mutualInformation p - mutualInformation lawT := by
  classical
  dsimp only
  intro independent
  let difference : Finset Index := T \ S
  let joinT :
      ((forall i : S, Output i.1) ×
        (forall i : difference, Output i.1)) ≃
          (forall i : T, Output i.1) := by
    let raw := Equiv.piFinsetUnion Output
      (Finset.disjoint_sdiff : Disjoint S (T \ S))
    rw [Finset.union_sdiff_of_subset subset] at raw
    exact raw
  have freshS : e ∉ S := fun member => fresh (subset member)
  let insertIndexT := Finset.subtypeInsertEquivOption fresh
  let reindexAddedT := insertIndexT.piCongrLeft'
    (fun i : (insert e T : Finset Index) => Output i.1)
  let splitAddedT := reindexAddedT.trans
    (Equiv.piOptionEquivProd
      (β := fun option : Option T => Output (insertIndexT.symm option).1))
  let joinAddedT :
      ((forall i : T, Output i.1) × Output e) ≃
        (forall i : (insert e T : Finset Index), Output i.1) :=
    (Equiv.prodComm _ _).trans splitAddedT.symm
  let insertIndexS := Finset.subtypeInsertEquivOption freshS
  let reindexAddedS := insertIndexS.piCongrLeft'
    (fun i : (insert e S : Finset Index) => Output i.1)
  let splitAddedS := reindexAddedS.trans
    (Equiv.piOptionEquivProd
      (β := fun option : Option S => Output (insertIndexS.symm option).1))
  let joinAddedS :
      ((forall i : S, Output i.1) × Output e) ≃
        (forall i : (insert e S : Finset Index), Output i.1) :=
    (Equiv.prodComm _ _).trans splitAddedS.symm
  let contextLaw :
      (((forall i : S, Output i.1) × Hidden) ×
        ((forall i : difference, Output i.1) × Output e)) -> Real :=
    fun value =>
      p (value.1.2,
        joinAddedT (joinT (value.1.1, value.2.1), value.2.2))
  let lawS : Hidden × (forall i : S, Output i.1) -> Real := fun value =>
    ∑ extra, ∑ added,
      p (value.1, joinAddedT (joinT (value.2, extra), added))
  let lawSE :
      Hidden × (forall i : (insert e S : Finset Index), Output i.1) -> Real :=
    fun value =>
      let separated := joinAddedS.symm value.2
      ∑ extra,
        p (value.1,
          joinAddedT (joinT (separated.1, extra), separated.2))
  let lawT : Hidden × (forall i : T, Output i.1) -> Real := fun value =>
    ∑ added, p (value.1, joinAddedT (value.2, added))
  let splitMass :
      (forall i : S, Output i.1) ×
          ((forall i : difference, Output i.1) × (Hidden × Output e)) ≃
        Hidden × (forall i : (insert e T : Finset Index), Output i.1) :=
    { toFun := fun value =>
        (value.2.2.1,
          joinAddedT (joinT (value.1, value.2.1), value.2.2.2))
      invFun := fun value =>
        let separatedT := joinAddedT.symm value.2
        let separatedSDifference := joinT.symm separatedT.1
        (separatedSDifference.1,
          (separatedSDifference.2, (value.1, separatedT.2)))
      left_inv := by
        intro value
        simp only
        rw [joinAddedT.symm_apply_apply, joinT.symm_apply_apply]
      right_inv := by
        intro value
        simp only
        rw [joinT.apply_symm_apply, joinAddedT.apply_symm_apply] }
  have splitMass_apply
      (selected : forall i : S, Output i.1)
      (extra : forall i : difference, Output i.1)
      (hidden : Hidden) (added : Output e) :
      splitMass (selected, (extra, (hidden, added))) =
        (hidden, joinAddedT (joinT (selected, extra), added)) := rfl
  let pSplit :
      (forall i : S, Output i.1) ×
          ((forall i : difference, Output i.1) × (Hidden × Output e)) -> Real :=
    fun value => p (splitMass value)
  have hpSplit :
      (forall value, 0 <= pSplit value) /\ ∑ value, pSplit value = 1 := by
    constructor
    · exact fun value => hp.1 (splitMass value)
    · rw [← hp.2]
      exact Fintype.sum_equiv splitMass _ _ (fun _ => rfl)
  have independentSplit :
      let splitContextLaw :
          (((forall i : S, Output i.1) × Hidden) ×
            ((forall i : difference, Output i.1) × Output e)) -> Real :=
        fun value =>
          pSplit (value.1.1, (value.2.1, (value.1.2, value.2.2)))
      forall context, marginal splitContextLaw context ≠ 0 ->
        conditional splitContextLaw context =
          fun value : (forall i : difference, Output i.1) × Output e =>
            marginal (conditional splitContextLaw context) value.1 *
              marginal
                (fun swapped : Output e ×
                    (forall i : difference, Output i.1) =>
                  conditional splitContextLaw context
                    (swapped.2, swapped.1)) value.2 := by
    simpa only [pSplit, splitMass_apply, contextLaw, difference] using independent
  let oldLawS : Hidden × (forall i : S, Output i.1) -> Real := fun value =>
    ∑ extra, ∑ added,
      pSplit (value.2, (extra, (value.1, added)))
  let oldLawSE :
      Hidden × ((forall i : S, Output i.1) × Output e) -> Real := fun value =>
    ∑ extra, pSplit (value.2.1, (extra, (value.1, value.2.2)))
  let oldLawT :
      Hidden × ((forall i : S, Output i.1) ×
        (forall i : difference, Output i.1)) -> Real := fun value =>
    ∑ added, pSplit (value.2.1, (value.2.2, (value.1, added)))
  let oldLawTE :
      Hidden × (((forall i : S, Output i.1) ×
        (forall i : difference, Output i.1)) × Output e) -> Real := fun value =>
    pSplit (value.2.1.1, (value.2.1.2, (value.1, value.2.2)))
  have core :
      mutualInformation oldLawSE - mutualInformation oldLawS >=
        mutualInformation oldLawTE - mutualInformation oldLawT := by
    simpa only [oldLawS, oldLawSE, oldLawT, oldLawTE] using
      conditional_information_diminishes_of_product_slices
        pSplit hpSplit independentSplit
  have lawSIdentity : oldLawS = lawS := by
    rfl
  have lawSENonnegative : forall value, 0 <= lawSE value := by
    intro value
    exact Finset.sum_nonneg fun extra _ => hp.1 _
  have lawSEIdentity : mutualInformation oldLawSE = mutualInformation lawSE := by
    have reindexed := mutual_information_reindex_right
      joinAddedS lawSE lawSENonnegative
    simpa only [oldLawSE, lawSE, pSplit, splitMass_apply,
      joinAddedS.symm_apply_apply] using reindexed
  have lawTNonnegative : forall value, 0 <= lawT value := by
    intro value
    exact Finset.sum_nonneg fun added _ => hp.1 _
  have lawTIdentity : mutualInformation oldLawT = mutualInformation lawT := by
    have reindexed := mutual_information_reindex_right joinT lawT lawTNonnegative
    simpa only [oldLawT, lawT, pSplit, splitMass_apply] using reindexed
  let joinFull :
      (((forall i : S, Output i.1) ×
        (forall i : difference, Output i.1)) × Output e) ≃
          (forall i : (insert e T : Finset Index), Output i.1) :=
    (joinT.prodCongr (Equiv.refl (Output e))).trans joinAddedT
  have joinFull_apply
      (value : ((forall i : S, Output i.1) ×
        (forall i : difference, Output i.1)) × Output e) :
      joinFull value = joinAddedT (joinT value.1, value.2) := rfl
  have lawTEIdentity : mutualInformation oldLawTE = mutualInformation p := by
    have reindexed := mutual_information_reindex_right joinFull p hp.1
    simpa only [oldLawTE, pSplit, splitMass_apply, joinFull_apply] using reindexed
  rw [lawSIdentity, lawSEIdentity, lawTIdentity, lawTEIdentity] at core
  exact core

#print axioms canonical_conditional_information_submodular

end D5.S3.Entropy.Submodularity.CanonicalConditionalInformationSubmodularity
