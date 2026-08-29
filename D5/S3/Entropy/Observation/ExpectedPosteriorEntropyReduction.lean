/- GID: D5/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction
   generality: G
   mirror-B: D5/B/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite information gain is prior entropy minus expected posterior entropy. -/

/- Library-search audit trail (2026-08-29):
   * Repository name and body searches covered mutual information, information gain,
     posterior entropy, conditional entropy, Bayes updates, and expectation-shaped sums.
   * The digest atom remains residual-open. No existing declaration states the channel/prior
     identity below or names its information-gain and expected-posterior-entropy quantities.
   * `mutual_information_eq_entropy_sub` gives the three-entropy expansion for a joint law,
     while `entropy_chain_rule` identifies joint entropy with marginal plus conditional entropy.
     Both are applied below. `conditionalEntropy`, `channelOutput`, and `posterior` remain the
     unique sources for the weighted conditional entropy and Bayes update.
   * Pinned Mathlib `InformationTheory/` has measure-valued KL chain rules but no finite Shannon
     mutual-information identity. `Probability/Kernel/Posterior` defines a measure-kernel
     posterior but has no finite real-valued entropy bridge matching this statement.
   * The generalization search found the two joint-law identities above, not a theorem connecting
     a finite prior and channel to their observation-first joint law and posterior entropy.
-/

import D5.S3.Entropy.ConditionalEntropy
import D5.S3.Entropy.MutualInformationEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.Observation.ExpectedPosteriorEntropyReduction

open D5.S3.Divergence.ChainRule
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy

/-- The observation-first joint mass induced by a prior and finite experiment channel. -/
noncomputable def experimentJointLaw {X Y : Type*}
    (channel : X -> Y -> Real) (prior : X -> Real) : Y × X -> Real :=
  fun pair => prior pair.2 * channel pair.2 pair.1

/-- Information gain of a finite experiment, evaluated as mutual information in nats. -/
noncomputable def informationGain {X Y : Type*} [Fintype X] [Fintype Y]
    (channel : X -> Y -> Real) (prior : X -> Real) : Real :=
  mutualInformation (experimentJointLaw channel prior)

/-- Output-marginal expectation of the Shannon entropy of the Bayes posterior. -/
noncomputable def expectedPosteriorEntropy {X Y : Type*} [Fintype X] [Fintype Y]
    (channel : X -> Y -> Real) (prior : X -> Real) : Real :=
  ∑ y, channelOutput channel prior y * shannonEntropy (posterior channel prior y)

/-- For finite state and observation types, experiment information gain is prior entropy minus
the output-marginal expectation of posterior entropy. No normalization of the prior is needed for
this finite algebraic identity. -/
theorem information_gain_eq_expected_entropy_reduction
    {X Y : Type*} [Fintype X] [Fintype Y]
    (channel : X -> Y -> Real) (prior : X -> Real)
    (jointNonnegative : forall y x, 0 <= prior x * channel x y)
    (channelNormalized : forall x, (∑ y, channel x y) = 1) :
    informationGain channel prior =
      shannonEntropy prior - expectedPosteriorEntropy channel prior := by
  let joint : Y × X -> Real := experimentJointLaw channel prior
  have hJoint : forall pair, 0 <= joint pair := by
    intro pair
    exact jointNonnegative pair.1 pair.2
  have hPriorMarginal :
      marginal (fun pair : X × Y => joint (pair.2, pair.1)) = prior := by
    funext x
    simp only [joint, experimentJointLaw, marginal]
    rw [<- Finset.mul_sum, channelNormalized x, mul_one]
  have hPosteriorEntropy :
      conditionalEntropy joint = expectedPosteriorEntropy channel prior := by
    rfl
  have hMutualInformation := mutual_information_eq_entropy_sub joint hJoint
  have hChainRule := entropy_chain_rule joint hJoint
  rw [hPriorMarginal] at hMutualInformation
  rw [hPosteriorEntropy] at hChainRule
  change mutualInformation joint =
    shannonEntropy prior - expectedPosteriorEntropy channel prior
  linarith

#print axioms information_gain_eq_expected_entropy_reduction

/-- Nonnegativity of the induced joint weights cannot be dropped from the general theorem. -/
theorem joint_nonnegativity_is_necessary :
    let prior : Option Bool -> Real := fun state =>
      match state with
      | none => -2
      | some _ => 1
    let channel : Option Bool -> Unit -> Real := fun _ _ => 1
    (forall x, (∑ y, channel x y) = 1) /\
      (¬(forall y x, 0 <= prior x * channel x y)) /\
        informationGain channel prior ≠
          shannonEntropy prior - expectedPosteriorEntropy channel prior := by
  dsimp only
  constructor
  · simp
  constructor
  · intro nonnegative
    have impossible := nonnegative () none
    norm_num at impossible
  · simp only [informationGain, experimentJointLaw, mutualInformation, klDivergence,
      marginal, expectedPosteriorEntropy, channelOutput, posterior, shannonEntropy,
      Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_option, Fintype.sum_bool,
      Real.negMulLog]
    have hLogTwoPos : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
    norm_num [Real.log_neg_eq_log]

#print axioms joint_nonnegativity_is_necessary

/-- Unit row mass also does real work: a nonnegative row of mass two breaks the identity. -/
theorem channel_normalization_is_necessary :
    let prior : Unit -> Real := fun _ => 1
    let channel : Unit -> Unit -> Real := fun _ _ => 2
    (forall y x, 0 <= prior x * channel x y) /\
      (¬(forall x, (∑ y, channel x y) = 1)) /\
        informationGain channel prior ≠
          shannonEntropy prior - expectedPosteriorEntropy channel prior := by
  dsimp only
  constructor
  · norm_num
  constructor
  · intro normalized
    have impossible := normalized ()
    norm_num at impossible
  · simp only [informationGain, experimentJointLaw, mutualInformation, klDivergence,
      marginal, expectedPosteriorEntropy, channelOutput, posterior, shannonEntropy,
      Fintype.sum_prod_type, Fintype.sum_unique, Real.negMulLog]
    have hLogHalf : Real.log (1 / 2 : Real) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    convert mul_ne_zero (show (2 : Real) ≠ 0 by norm_num) hLogHalf using 1 <;>
      norm_num

#print axioms channel_normalization_is_necessary

/- Degenerate audit: independent output, a revealing identity channel, a point prior, a singleton
output, and empty carriers are all covered by the finite statement. -/

example :
    let prior : Bool -> Real := fun _ => 1 / 2
    let channel : Bool -> Bool -> Real := fun _ _ => 1 / 2
    informationGain channel prior = 0 := by
  norm_num [informationGain, experimentJointLaw, mutualInformation, klDivergence, marginal,
    Fintype.sum_prod_type, Fintype.sum_bool]

example :
    let prior : Bool -> Real := fun _ => 1 / 2
    let channel : Bool -> Bool -> Real := fun x y => if x = y then 1 else 0
    informationGain channel prior = shannonEntropy prior := by
  norm_num [informationGain, experimentJointLaw, mutualInformation, klDivergence, marginal,
    shannonEntropy, Real.negMulLog, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, Real.log_inv]
  ring

example :
    let prior : Bool -> Real := fun x => if x then 0 else 1
    let channel : Bool -> Bool -> Real := fun x y => if x = y then 1 else 0
    informationGain channel prior = 0 := by
  norm_num [informationGain, experimentJointLaw, mutualInformation, klDivergence, marginal,
    Fintype.sum_prod_type, Fintype.sum_bool]

example (prior : Bool -> Real) (nonnegative : forall x, 0 <= prior x)
    (normalized : (∑ x, prior x) = 1) :
    informationGain (fun _ : Bool => fun _ : Unit => 1) prior = 0 := by
  have normalizedBool : prior true + prior false = 1 := by
    simpa only [Fintype.sum_bool] using normalized
  have posteriorEq :
      posterior (fun _ : Bool => fun _ : Unit => 1) prior () = prior := by
    funext x
    simp [posterior, channelOutput, normalizedBool]
  have expectedEq :
      expectedPosteriorEntropy (fun _ : Bool => fun _ : Unit => 1) prior =
        shannonEntropy prior := by
    simp [expectedPosteriorEntropy, channelOutput, normalizedBool, posteriorEq]
  have reduction := information_gain_eq_expected_entropy_reduction
    (fun _ : Bool => fun _ : Unit => 1) prior (by
      intro _ x
      simpa using nonnegative x) (by simp)
  rw [expectedEq] at reduction
  linarith

example :
    let prior : Bool -> Real := fun _ => 1 / 2
    let channel : Bool -> Bool -> Real := fun _ _ => 0
    informationGain channel prior ≠
      shannonEntropy prior - expectedPosteriorEntropy channel prior := by
  norm_num [informationGain, experimentJointLaw, mutualInformation, klDivergence, marginal,
    expectedPosteriorEntropy, channelOutput, posterior, shannonEntropy, Real.negMulLog,
    Fintype.sum_prod_type, Fintype.sum_bool]

example :
    informationGain (X := Empty) (Y := Empty)
      (fun state _ => nomatch state) (fun state => nomatch state) = (0 : Real) := by
  simp [informationGain, mutualInformation, klDivergence]

end D5.S3.Entropy.Observation.ExpectedPosteriorEntropyReduction
