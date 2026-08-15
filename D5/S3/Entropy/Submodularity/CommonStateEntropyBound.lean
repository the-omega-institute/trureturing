/- GID: D5/S3/Entropy/Submodularity/CommonStateEntropyBound
   generality: G
   mirror-B: D5/B/S3/Entropy/Submodularity/CommonStateEntropyBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound the entropy of a state determined by either coordinate by mutual information. -/

import D5.S3.Entropy.Forgetting.CapacityMonotone
import D5.S3.Entropy.Submodularity.MarkovDataProcessing

/- Library-search audit trail (2026-08-15):
   * Loogle queries `"mutualInformation"` and `"conditionalEntropy"` each found zero
     pinned-Mathlib declarations. The broader `"entropy"` query returned only scalar binary and
     q-ary entropy results, not finite-law mutual information or a common-state bound.
   * LeanSearch query `Shannon entropy of a common deterministic function is bounded by mutual
     information` returned scalar binary-entropy and measure-valued divergence results, with no
     matching theorem. Pinned-Mathlib grep likewise found no finite Shannon mutual-information API.
   * Repository searches for common/shared deterministic functions with mutual information or
     entropy found no duplicate. The proof imports and applies the exact repository support hit
     `mutual_information_le_of_markov`, then uses `mutual_information_eq_entropy_sub` to identify
     the information in a graph-supported law with the entropy of its deterministic output.
-/

namespace D5.S3.Entropy.Submodularity.CommonStateEntropyBound

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy
open D5.S3.Entropy.Submodularity.StrongSubadditivity
open D5.S3.Entropy.Submodularity.MarkovDataProcessing

private noncomputable def graphLaw {X C : Type*} (r : X -> Real) (f : X -> C) :
    X × C -> Real := by
  classical
  exact fun q => if f q.1 = q.2 then r q.1 else 0

private theorem graphLaw_nonneg {X C : Type*} (r : X -> Real) (f : X -> C)
    (hr : forall x, 0 ≤ r x) : forall q, 0 ≤ graphLaw r f q := by
  intro q
  classical
  simp only [graphLaw]
  split_ifs
  · exact hr q.1
  · exact le_rfl

private theorem marginal_graphLaw {X C : Type*} [Fintype C]
    (r : X -> Real) (f : X -> C) :
    marginal (graphLaw r f) = r := by
  classical
  funext x
  simp [marginal, graphLaw]

private theorem swapped_marginal_graphLaw {X C : Type*} [Fintype X]
    (r : X -> Real) (f : X -> C) :
    marginal (fun q : C × X => graphLaw r f (q.2, q.1)) = pushforward f r := by
  classical
  funext c
  simp only [marginal, graphLaw, pushforward]

private theorem entropy_graphLaw {X C : Type*} [Fintype X] [Fintype C]
    (r : X -> Real) (f : X -> C) :
    shannonEntropy (graphLaw r f) = shannonEntropy r := by
  classical
  rw [shannonEntropy, Fintype.sum_prod_type, shannonEntropy]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (f x)]
  · simp [graphLaw]
  · intro c _ hcx
    simp [graphLaw, Ne.symm hcx]
  · simp

private theorem mutual_information_graphLaw_eq_entropy {X C : Type*}
    [Fintype X] [Fintype C] (r : X -> Real) (f : X -> C)
    (hr : forall x, 0 ≤ r x) :
    mutualInformation (graphLaw r f) = shannonEntropy (pushforward f r) := by
  rw [mutual_information_eq_entropy_sub _ (graphLaw_nonneg r f hr),
    marginal_graphLaw, swapped_marginal_graphLaw, entropy_graphLaw]
  ring

private noncomputable def deterministicExtension {X Y C : Type*}
    (p : X × Y -> Real) (f : Y -> C) : X × (Y × C) -> Real := by
  classical
  exact fun q => p (q.1, q.2.1) * if f q.2.1 = q.2.2 then 1 else 0

private theorem deterministicExtension_is_law {X Y C : Type*}
    [Fintype X] [Fintype Y] [Fintype C]
    (p : X × Y -> Real) (f : Y -> C)
    (hp : (forall q, 0 ≤ p q) ∧ ∑ q, p q = 1) :
    (forall q, 0 ≤ deterministicExtension p f q) ∧
      ∑ q, deterministicExtension p f q = 1 := by
  classical
  constructor
  · intro q
    apply mul_nonneg (hp.1 _)
    split_ifs <;> norm_num
  · simp only [Fintype.sum_prod_type]
    calc
      (∑ x, ∑ y, ∑ c, deterministicExtension p f (x, (y, c))) =
          ∑ x, ∑ y, p (x, y) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            simp [deterministicExtension]
      _ = 1 := by simpa only [Fintype.sum_prod_type] using hp.2

private theorem xyProjection_deterministicExtension {X Y C : Type*}
    [Fintype C] (p : X × Y -> Real) (f : Y -> C) :
    xyProjection (deterministicExtension p f) = p := by
  classical
  funext q
  simp [xyProjection, deterministicExtension]

private theorem xzProjection_deterministicExtension {X Y C : Type*}
    [Fintype Y] (p : X × Y -> Real) (commonX : X -> C) (commonY : Y -> C)
    (hcommon : forall x y, p (x, y) ≠ 0 -> commonX x = commonY y) :
    xzProjection (deterministicExtension p commonY) =
      graphLaw (marginal p) commonX := by
  classical
  funext q
  simp only [xzProjection, deterministicExtension, graphLaw]
  by_cases hxc : commonX q.1 = q.2
  · rw [if_pos hxc, marginal]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hpy : p (q.1, y) = 0
    · simp [hpy]
    · have hyc : commonY y = q.2 := (hcommon q.1 y hpy).symm.trans hxc
      simp [hyc]
  · rw [if_neg hxc]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hpy : p (q.1, y) = 0
    · simp [hpy]
    · have hyc : commonY y ≠ q.2 := by
        intro hyc
        exact hxc ((hcommon q.1 y hpy).trans hyc)
      simp [hyc]

private theorem deterministicExtension_is_markov {X Y C : Type*}
    [Fintype X] [Fintype C] (p : X × Y -> Real) (f : Y -> C) :
    forall x y c,
      deterministicExtension p f (x, (y, c)) *
          marginal (yFirstLaw (deterministicExtension p f)) y =
        xyProjection (deterministicExtension p f) (x, y) *
          xzProjection (yFirstLaw (deterministicExtension p f)) (y, c) := by
  classical
  have hchannel : forall y, ∑ c, (if f y = c then (1 : Real) else 0) = 1 := by
    intro y
    simp
  have hextension : deterministicExtension p f =
      fun q => p (q.1, q.2.1) * if f q.2.1 = q.2.2 then 1 else 0 := by
    funext q
    simp only [deterministicExtension]
  rw [hextension]
  exact markov_of_channel p (fun y c => if f y = c then (1 : Real) else 0) hchannel

/-- If a finite state is determined by either coordinate of a joint law, then the Shannon
entropy of that common state is at most the mutual information between the coordinates. -/
theorem common_state_entropy_le_mutual_information
    {X Y C : Type*} [Fintype X] [Fintype Y] [Fintype C]
    (p : X × Y -> Real)
    (hp : (forall q, 0 ≤ p q) ∧ ∑ q, p q = 1)
    (commonX : X -> C) (commonY : Y -> C)
    (hcommon : forall x y, p (x, y) ≠ 0 -> commonX x = commonY y) :
    shannonEntropy (pushforward commonX (marginal p)) ≤ mutualInformation p := by
  have hmarginal_nonneg : forall x, 0 ≤ marginal p x := by
    intro x
    rw [marginal]
    exact Finset.sum_nonneg fun y _ => hp.1 (x, y)
  have hdata := mutual_information_le_of_markov
    (deterministicExtension p commonY)
    (deterministicExtension_is_law p commonY hp)
    (deterministicExtension_is_markov p commonY)
  rw [xyProjection_deterministicExtension,
    xzProjection_deterministicExtension p commonX commonY hcommon,
    mutual_information_graphLaw_eq_entropy _ _ hmarginal_nonneg] at hdata
  exact hdata

-- A shared fair Boolean state witnesses the hypotheses on a nontrivial common-state law.
example :
    let p : Bool × Bool -> Real := fun q => if q.1 = q.2 then 1 / 2 else 0
    shannonEntropy (pushforward id (marginal p)) ≤ mutualInformation p := by
  dsimp
  apply common_state_entropy_le_mutual_information (commonX := id) (commonY := id)
  · constructor
    · intro q
      split_ifs <;> norm_num
    · norm_num [Fintype.sum_prod_type, Fintype.sum_bool]
  · intro x y hxy
    have hxy_eq : x = y := by
      by_contra hne
      exact hxy (by simp [hne])
    exact congrArg id hxy_eq

end D5.S3.Entropy.Submodularity.CommonStateEntropyBound
