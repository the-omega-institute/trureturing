/- GID: D5/S3/Entropy/Submodularity/RefinementInformationDecomposition
   generality: G
   mirror-B: D5/B/S3/Entropy/Submodularity/RefinementInformationDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Decompose predictive memory exactly across a finer deterministic readout. -/

/- Library-search audit trail (2026-08-22):
   * Repository searches for `conditionalMutualInformation`, conditional chain rules, and
     refinement decompositions found the frozen entropy-defect and nonnegativity theorems below,
     but no theorem stating this deterministic-readout decomposition.
   * The exact hits `conditional_mutual_information_eq_entropy_defect` and
     `conditional_mutual_information_nonneg` are applied directly. The frozen unconditional
     `mutual_information_chain_rule` has a different conditioning shape.
   * Pinned Mathlib has no finite real-valued conditional-mutual-information interface matching
     these repository definitions.
-/

import D5.S3.Entropy.Forgetting.CapacityMonotone
import D5.S3.Entropy.Submodularity.MutualInformationChainRule

namespace D5.S3.Entropy.Submodularity.RefinementInformationDecomposition

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation
open D5.S3.Entropy.Submodularity.StrongSubadditivity

/-- The joint law of a deterministic readout, the past, and the future. -/
noncomputable def readoutPastFutureLaw {P F C : Type*}
    (p : P × F -> Real) (readout : P -> C) : C × (P × F) -> Real := by
  classical
  exact fun z => if readout z.2.1 = z.1 then p (z.2.1, z.2.2) else 0

/-- The joint law of a deterministic readout and the future. -/
noncomputable def readoutFutureLaw {P F C : Type*} [Fintype P]
    (p : P × F -> Real) (readout : P -> C) : C × F -> Real := by
  classical
  exact fun z => ∑ past, if readout past = z.1 then p (past, z.2) else 0

/-- Predictive memory retained beyond a deterministic readout of the past. -/
noncomputable def predictiveMemory {P F C : Type*}
    [Fintype C] [Fintype P] [Fintype F]
    (p : P × F -> Real) (readout : P -> C) : Real :=
  conditionalMutualInformation (readoutPastFutureLaw p readout)

/-- Information gained by replacing a coarse readout with a finer deterministic readout. -/
noncomputable def refinementGain {P F Fine Coarse : Type*}
    [Fintype P] [Fintype F] [Fintype Fine] [Fintype Coarse]
    (p : P × F -> Real) (fine : P -> Fine) (forget : Fine -> Coarse) : Real :=
  conditionalMutualInformation
    (readoutPastFutureLaw (readoutFutureLaw p fine) forget)

private noncomputable def graphLaw {X C : Type*}
    (r : X -> Real) (readout : X -> C) : C × X -> Real := by
  classical
  exact fun z => if readout z.2 = z.1 then r z.2 else 0

private theorem readoutPastFutureLaw_nonneg {P F C : Type*}
    (p : P × F -> Real) (readout : P -> C) (hp : forall z, 0 <= p z) :
    forall z, 0 <= readoutPastFutureLaw p readout z := by
  intro z
  classical
  simp only [readoutPastFutureLaw]
  split_ifs
  · exact hp _
  · exact le_rfl

private theorem readoutFutureLaw_nonneg {P F C : Type*} [Fintype P]
    (p : P × F -> Real) (readout : P -> C) (hp : forall z, 0 <= p z) :
    forall z, 0 <= readoutFutureLaw p readout z := by
  intro z
  classical
  simp only [readoutFutureLaw]
  exact Finset.sum_nonneg fun past _ => by
    split_ifs
    · exact hp _
    · exact le_rfl

private theorem readoutPastFutureLaw_is_law {P F C : Type*}
    [Fintype P] [Fintype F] [Fintype C]
    (p : P × F -> Real) (readout : P -> C)
    (hp : (forall z, 0 <= p z) /\ ∑ z, p z = 1) :
    (forall z, 0 <= readoutPastFutureLaw p readout z) /\
      ∑ z, readoutPastFutureLaw p readout z = 1 := by
  classical
  refine ⟨readoutPastFutureLaw_nonneg p readout hp.1, ?_⟩
  simp only [Fintype.sum_prod_type, readoutPastFutureLaw]
  calc
    (∑ c, ∑ past, ∑ future,
        if readout past = c then p (past, future) else 0) =
        ∑ past, ∑ future, ∑ c,
          if readout past = c then p (past, future) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro past _
      rw [Finset.sum_comm]
    _ = ∑ past, ∑ future, p (past, future) := by simp
    _ = 1 := by simpa only [Fintype.sum_prod_type] using hp.2

private theorem readoutFutureLaw_is_law {P F C : Type*}
    [Fintype P] [Fintype F] [Fintype C]
    (p : P × F -> Real) (readout : P -> C)
    (hp : (forall z, 0 <= p z) /\ ∑ z, p z = 1) :
    (forall z, 0 <= readoutFutureLaw p readout z) /\
      ∑ z, readoutFutureLaw p readout z = 1 := by
  classical
  refine ⟨readoutFutureLaw_nonneg p readout hp.1, ?_⟩
  simp only [Fintype.sum_prod_type, readoutFutureLaw]
  calc
    (∑ c, ∑ future, ∑ past,
        if readout past = c then p (past, future) else 0) =
        ∑ c, ∑ past, ∑ future,
          if readout past = c then p (past, future) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ past, ∑ c, ∑ future,
          if readout past = c then p (past, future) else 0 := Finset.sum_comm
    _ =
        ∑ past, ∑ future, ∑ c,
          if readout past = c then p (past, future) else 0 := by
      apply Finset.sum_congr rfl
      intro past _
      rw [Finset.sum_comm]
    _ = ∑ past, ∑ future, p (past, future) := by simp
    _ = 1 := by simpa only [Fintype.sum_prod_type] using hp.2

private theorem xyProjection_readoutPastFutureLaw {P F C : Type*}
    [Fintype F] (p : P × F -> Real) (readout : P -> C) :
    xyProjection (readoutPastFutureLaw p readout) =
      graphLaw (marginal p) readout := by
  classical
  funext z
  simp only [xyProjection, readoutPastFutureLaw, graphLaw, marginal]
  by_cases h : readout z.2 = z.1 <;> simp [h]

private theorem xzProjection_readoutPastFutureLaw {P F C : Type*}
    [Fintype P] (p : P × F -> Real) (readout : P -> C) :
    xzProjection (readoutPastFutureLaw p readout) = readoutFutureLaw p readout := by
  classical
  funext z
  simp only [xzProjection, readoutPastFutureLaw, readoutFutureLaw]

private theorem marginal_readoutPastFutureLaw {P F C : Type*}
    [Fintype P] [Fintype F] (p : P × F -> Real) (readout : P -> C) :
    marginal (readoutPastFutureLaw p readout) =
      pushforward readout (marginal p) := by
  classical
  funext c
  simp only [marginal, readoutPastFutureLaw, pushforward, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro past _
  by_cases h : readout past = c <;> simp [h]

private theorem entropy_graphLaw {X C : Type*} [Fintype X] [Fintype C]
    (r : X -> Real) (readout : X -> C) :
    shannonEntropy (graphLaw r readout) = shannonEntropy r := by
  classical
  rw [shannonEntropy, Fintype.sum_prod_type, shannonEntropy]
  calc
    (∑ c, ∑ x, Real.negMulLog
        (if readout x = c then r x else 0)) =
        ∑ x, ∑ c, Real.negMulLog
          (if readout x = c then r x else 0) := Finset.sum_comm
    _ = ∑ x, Real.negMulLog (r x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single (readout x)]
      · simp
      · intro c _ h
        simp [Ne.symm h]
      · simp

private theorem entropy_readoutPastFutureLaw {P F C : Type*}
    [Fintype P] [Fintype F] [Fintype C]
    (p : P × F -> Real) (readout : P -> C) :
    shannonEntropy (readoutPastFutureLaw p readout) = shannonEntropy p := by
  classical
  simp only [shannonEntropy, readoutPastFutureLaw, Fintype.sum_prod_type]
  calc
    (∑ c, ∑ past, ∑ future, Real.negMulLog
        (if readout past = c then p (past, future) else 0)) =
        ∑ past, ∑ future, ∑ c, Real.negMulLog
          (if readout past = c then p (past, future) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro past _
      rw [Finset.sum_comm]
    _ = ∑ past, ∑ future, Real.negMulLog (p (past, future)) := by
      apply Finset.sum_congr rfl
      intro past _
      apply Finset.sum_congr rfl
      intro future _
      rw [Finset.sum_eq_single (readout past)]
      · simp
      · intro c _ h
        simp [Ne.symm h]
      · simp

private theorem predictiveMemory_entropy_balance {P F C : Type*}
    [Fintype P] [Fintype F] [Fintype C]
    (p : P × F -> Real) (readout : P -> C) (hp : forall z, 0 <= p z) :
    predictiveMemory p readout =
      shannonEntropy (marginal p) + shannonEntropy (readoutFutureLaw p readout) -
        shannonEntropy p - shannonEntropy (pushforward readout (marginal p)) := by
  rw [predictiveMemory,
    conditional_mutual_information_eq_entropy_defect _
      (readoutPastFutureLaw_nonneg p readout hp),
    xyProjection_readoutPastFutureLaw, xzProjection_readoutPastFutureLaw,
    entropy_graphLaw, entropy_readoutPastFutureLaw,
    marginal_readoutPastFutureLaw]

private theorem marginal_readoutFutureLaw {P F C : Type*}
    [Fintype P] [Fintype F] (p : P × F -> Real) (readout : P -> C) :
    marginal (readoutFutureLaw p readout) =
      pushforward readout (marginal p) := by
  classical
  funext c
  simp only [marginal, readoutFutureLaw, pushforward]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro past _
  by_cases h : readout past = c <;> simp [h]

private theorem readoutFutureLaw_comp {P F Fine Coarse : Type*}
    [Fintype P] [Fintype Fine]
    (p : P × F -> Real) (fine : P -> Fine) (forget : Fine -> Coarse) :
    readoutFutureLaw (readoutFutureLaw p fine) forget =
      readoutFutureLaw p (forget ∘ fine) := by
  classical
  funext z
  simp only [readoutFutureLaw, Function.comp_apply]
  calc
    (∑ c, if forget c = z.1 then
        ∑ past, if fine past = c then p (past, z.2) else 0 else 0) =
        ∑ c, ∑ past, if fine past = c /\ forget c = z.1 then
          p (past, z.2) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : forget c = z.1
      · simp [hc]
      · simp [hc]
    _ = ∑ past, ∑ c, if fine past = c /\ forget c = z.1 then
          p (past, z.2) else 0 := Finset.sum_comm
    _ = ∑ past, if forget (fine past) = z.1 then p (past, z.2) else 0 := by
      apply Finset.sum_congr rfl
      intro past _
      rw [Finset.sum_eq_single (fine past)]
      · simp
      · intro c _ h
        simp [Ne.symm h]
      · simp

private theorem pushforward_comp {X Y Z : Type*} [Fintype X] [Fintype Y]
    (p : X -> Real) (first : X -> Y) (second : Y -> Z) :
    pushforward second (pushforward first p) = pushforward (second ∘ first) p := by
  classical
  funext z
  simp only [pushforward, Function.comp_apply]
  calc
    (∑ y, if second y = z then
        ∑ x, if first x = y then p x else 0 else 0) =
        ∑ y, ∑ x, if first x = y /\ second y = z then p x else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : second y = z
      · simp [hy]
      · simp [hy]
    _ = ∑ x, ∑ y, if first x = y /\ second y = z then p x else 0 :=
      Finset.sum_comm
    _ = ∑ x, if second (first x) = z then p x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single (first x)]
      · simp
      · intro y _ h
        simp [Ne.symm h]
      · simp

/-- A finer deterministic readout decomposes predictive memory into its residual memory and a
nonnegative conditional-information gain. No independence between the past and the finer readout
is assumed: the finer readout is constructed directly as a function of the past. -/
theorem deterministic_refinement_information_decomposition
    {P F Fine Coarse : Type*}
    [Fintype P] [Fintype F] [Fintype Fine] [Fintype Coarse]
    (p : P × F -> Real)
    (hp : (forall z, 0 <= p z) /\ ∑ z, p z = 1)
    (fine : P -> Fine) (forget : Fine -> Coarse) :
    predictiveMemory p (forget ∘ fine) - predictiveMemory p fine =
        refinementGain p fine forget /\
      0 <= refinementGain p fine forget := by
  have hcoarse := predictiveMemory_entropy_balance p (forget ∘ fine) hp.1
  have hfine := predictiveMemory_entropy_balance p fine hp.1
  have hgain : refinementGain p fine forget =
      shannonEntropy (marginal (readoutFutureLaw p fine)) +
          shannonEntropy
            (readoutFutureLaw (readoutFutureLaw p fine) forget) -
        shannonEntropy (readoutFutureLaw p fine) -
          shannonEntropy
            (pushforward forget (marginal (readoutFutureLaw p fine))) :=
    predictiveMemory_entropy_balance
      (readoutFutureLaw p fine) forget (readoutFutureLaw_nonneg p fine hp.1)
  rw [marginal_readoutFutureLaw, readoutFutureLaw_comp,
    pushforward_comp] at hgain
  constructor
  · linarith
  · change 0 <= conditionalMutualInformation
      (readoutPastFutureLaw (readoutFutureLaw p fine) forget)
    exact conditional_mutual_information_nonneg
      (readoutPastFutureLaw (readoutFutureLaw p fine) forget)
      (readoutPastFutureLaw_is_law _ _ (readoutFutureLaw_is_law p fine hp))

-- A fair Boolean past/future law supplies a nontrivial finite witness for all public hypotheses.
example :
    let p : Bool × Bool -> Real := fun z => if z.1 = z.2 then 1 / 2 else 0
    predictiveMemory p (fun _ : Bool => ()) - predictiveMemory p id =
        refinementGain p id (fun _ => ()) /\
      0 <= refinementGain p id (fun _ => ()) := by
  dsimp only
  apply deterministic_refinement_information_decomposition
    (p := fun z : Bool × Bool => if z.1 = z.2 then 1 / 2 else 0)
    (fine := id) (forget := fun _ => ())
  constructor
  · intro z
    split_ifs <;> norm_num
  · norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

#print axioms deterministic_refinement_information_decomposition

end D5.S3.Entropy.Submodularity.RefinementInformationDecomposition
