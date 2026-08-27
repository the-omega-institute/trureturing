/- GID: D5/S3/Entropy/Forgetting/ConditionalInformationPostprocessing
   generality: G
   mirror-B: D5/B/S3/Entropy/Forgetting/ConditionalInformationPostprocessing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deterministic postprocessing cannot increase finite conditional mutual information. -/

import D5.S3.Entropy.Forgetting.CapacityMonotone
import D5.S3.Entropy.Submodularity.MutualInformationChainRule

/- Library-search audit trail (2026-08-27):
   * Repository searches found the canonical finite joint-law primitives
     `pushforward` and `conditionalMutualInformation`, but no theorem stating
     conditional data processing under deterministic postprocessing.
   * Exact component hits `mutual_information_chain_rule`,
     `mutual_information_le_of_markov`, and `markov_of_channel` reduce the
     conditional claim to the frozen finite Markov data-processing theorem.
   * Pinned Mathlib searches found measure-theoretic conditional independence
     and KL divergence, but no real-valued finite conditional-mutual-information
     interface matching this carrier. -/

noncomputable section

namespace D5.S3.Entropy.Forgetting.ConditionalInformationPostprocessing

open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation
open D5.S3.Entropy.Submodularity.MarkovDataProcessing
open D5.S3.Entropy.Submodularity.MutualInformationChainRule
open D5.S3.Entropy.Submodularity.StrongSubadditivity

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- For a finite joint law of a commitment, a future record, and an
environment, deterministic postprocessing of the future record cannot increase
its conditional mutual information with the commitment given the environment. -/
theorem conditional_mutual_information_postprocessing_le
    {C B B' E : Type*}
    [Fintype C] [Fintype B] [Fintype B'] [Fintype E]
    (p : E × (C × B) -> Real)
    (hp : (∀ x, 0 <= p x) ∧ ∑ x, p x = 1)
    (postprocess : B -> B') :
    let processed : E × (C × B') -> Real :=
      pushforward
        (fun x : E × (C × B) =>
          (x.1, (x.2.1, postprocess x.2.2))) p
    conditionalMutualInformation processed <=
      conditionalMutualInformation p := by
  classical
  let processed : E × (C × B') -> Real :=
    pushforward
      (fun x : E × (C × B) =>
        (x.1, (x.2.1, postprocess x.2.2))) p
  change conditionalMutualInformation processed <= conditionalMutualInformation p
  let raw : C × (E × B) -> Real :=
    fun x => p (x.2.1, (x.1, x.2.2))
  let processedRaw : C × (E × B') -> Real :=
    fun x => processed (x.2.1, (x.1, x.2.2))
  let coarse : E × B -> E × B' :=
    fun x => (x.1, postprocess x.2)
  let channel : (E × B) -> (E × B') -> Real :=
    fun source target => if coarse source = target then 1 else 0
  let extension : C × ((E × B) × (E × B')) -> Real :=
    fun x => raw (x.1, x.2.1) * channel x.2.1 x.2.2
  have raw_nonnegative : ∀ x, 0 <= raw x := fun x => hp.1 _
  have raw_normalized : ∑ x, raw x = 1 := by
    simp only [raw, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using hp.2
  have channel_normalized : ∀ source, ∑ target, channel source target = 1 := by
    intro source
    simp [channel]
  have extension_is_law :
      (∀ x, 0 <= extension x) ∧ ∑ x, extension x = 1 := by
    constructor
    · intro x
      exact mul_nonneg (raw_nonnegative _) (by
        simp only [channel]
        split_ifs <;> norm_num)
    · simp only [extension, Fintype.sum_prod_type, ← Finset.mul_sum,
        channel_normalized, mul_one]
      simpa only [Fintype.sum_prod_type] using raw_normalized
  have data_processing := mutual_information_le_of_markov
    extension extension_is_law
    (markov_of_channel raw channel channel_normalized)
  have extension_xy : xyProjection extension = raw := by
    funext x
    simp [xyProjection, extension, channel]
  have extension_xz : xzProjection extension = processedRaw := by
    funext x
    simp only [xzProjection, extension, processedRaw, processed, pushforward,
      raw, channel, coarse, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e = x.2.1
    · subst e
      rw [Finset.sum_eq_single x.1]
      · simp [Prod.ext_iff]
      · intro c _ hc
        simp [Prod.ext_iff, hc]
      · simp
    · simp [Prod.ext_iff, he]
  rw [extension_xy, extension_xz] at data_processing
  have raw_y_first : yFirstLaw raw = p := by
    funext x
    rfl
  have processed_raw_y_first : yFirstLaw processedRaw = processed := by
    funext x
    rfl
  have processed_raw_nonnegative : ∀ x, 0 <= processedRaw x := by
    intro x
    simp only [processedRaw, processed, pushforward]
    exact Finset.sum_nonneg fun source _ => by
      split_ifs
      · exact hp.1 source
      · exact le_rfl
  have xy_processed_eq : xyProjection processedRaw = xyProjection raw := by
    funext x
    simp only [xyProjection, processedRaw, processed, pushforward, raw,
      Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single x.2]
    · calc
        _ = ∑ output, ∑ b,
              if postprocess b = output then p (x.2, x.1, b) else 0 := by
          apply Finset.sum_congr rfl
          intro output _
          rw [Finset.sum_eq_single x.1]
          · simp [Prod.ext_iff]
          · intro c _ hc
            simp [Prod.ext_iff, hc]
          · simp
        _ = ∑ b, p (x.2, x.1, b) := by
          rw [Finset.sum_comm]
          simp
    · intro e _ he
      simp [Prod.ext_iff, he]
    · simp
  have before_chain := mutual_information_chain_rule raw raw_nonnegative
  have after_chain :=
    mutual_information_chain_rule processedRaw processed_raw_nonnegative
  rw [raw_y_first] at before_chain
  rw [processed_raw_y_first, xy_processed_eq] at after_chain
  linarith

#print axioms conditional_mutual_information_postprocessing_le

end D5.S3.Entropy.Forgetting.ConditionalInformationPostprocessing
