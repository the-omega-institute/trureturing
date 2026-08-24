/- GID: D5/S3/Entropy/Observation/CompletionInformationChainDecomposition
   generality: G
   mirror-B: D5/B/S3/Entropy/Observation/CompletionInformationChainDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Decompose observation entropy and identify stable completion information. -/

/- Library-search audit trail (2026-08-24):
   * Pinned-Mathlib searches for finite Shannon entropy, conditional entropy, and finite entropy
     chain rules found only measure-valued KL chain rules; no finite real-valued Shannon result
     matched the statement.
   * The repository exact hits `entropy_chain_rule`, `shannonEntropy_extend_injective`,
     `futureReadoutWord`, `finiteWordRangeEquiv`, and `stableCompletionEquiv` are imported and
     applied below. Repository search found no iterated observation-word chain rule or stable
     completion conditional-entropy identity.
   * The observation laws below are deterministic pushforwards of the initial law through the
     update/readout dynamics. The stable equivalence composes the canonical kernel-range and
     stable-quotient equivalences; neither object is defined from an entropy equality.
-/

import D5.S3.Entropy.Forgetting.CapacityMonotone
import D5.S3.Entropy.Relabeling.InjectiveInvariance
import D5.S3.ObserverMemory.Refinement.GradedPredictionShift

namespace D5.S3.Entropy.Observation.CompletionInformationChainDecomposition

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Relabeling.InjectiveInvariance
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Refinement.GradedPredictionShift
open D5.S3.ObserverMemory.Refinement.PredictionCompletion
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The law of the readout at the initial time. -/
noncomputable def initialReadoutLaw {Y O : Type*} [Fintype Y]
    (readout : Y -> O) (initial : Y -> Real) : O -> Real :=
  pushforward readout initial

/-- The law of the observation word from time zero through `depth`. -/
noncomputable def observationWordLaw {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O) (initial : Y -> Real)
    (depth : Nat) : (Fin (depth + 1) -> O) -> Real :=
  pushforward (futureReadoutWord update readout depth) initial

/-- The joint law of the observation word through `depth` and the next readout. -/
noncomputable def observationIncrementJointLaw {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O) (initial : Y -> Real)
    (depth : Nat) : ((Fin (depth + 1) -> O) × O) -> Real :=
  pushforward
    (fun y =>
      (futureReadoutWord update readout depth y,
        readout ((update^[depth + 1]) y))) initial

/-- The joint law of the initial readout and the canonical completed state. -/
noncomputable def completionObservationJointLaw {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O) (initial : Y -> Real) :
    O × CompletedState update readout -> Real :=
  pushforward
    (fun y => (readout y, completionProjection update readout y)) initial

/-- At an adjacent-partition stable depth, the realized observation words are canonically
equivalent to the complete-future quotient. -/
noncomputable def stableObservationCompletionEquiv {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (depth : Nat)
    (hstable :
      Setoid.ker (futureReadoutWord update readout depth) =
        Setoid.ker (futureReadoutWord update readout (depth + 1))) :
    Set.range (futureReadoutWord update readout depth) ≃
      CompletedState update readout :=
  (finiteWordRangeEquiv update readout depth).symm.trans
    (stableCompletionEquiv update readout depth hstable)

private theorem pushforward_comp {X A B : Type*} [Fintype X] [Fintype A]
    (p : X -> Real) (f : X -> A) (g : A -> B) :
    pushforward g (pushforward f p) = pushforward (g ∘ f) p := by
  classical
  funext b
  simp only [pushforward]
  calc
    (∑ a, if g a = b then ∑ x, if f x = a then p x else 0 else 0) =
        ∑ a, ∑ x, if g a = b then (if f x = a then p x else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : g a = b <;> simp [ha]
    _ = ∑ x, ∑ a, if g a = b then (if f x = a then p x else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ x, if (g ∘ f) x = b then p x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single (f x)]
      · simp
      · intro a _ ha
        simp [Ne.symm ha]
      · simp

private theorem entropy_pushforward_injective {A B : Type*}
    [Fintype A] [Fintype B]
    (p : A -> Real) (f : A -> B) (hf : Function.Injective f) :
    shannonEntropy (pushforward f p) = shannonEntropy p := by
  classical
  have hpushforward :
      pushforward f p = Function.extend f p (fun _ => 0) := by
    funext b
    by_cases hb : b ∈ Set.range f
    · rcases hb with ⟨a, rfl⟩
      rw [hf.extend_apply]
      simp only [pushforward]
      rw [Finset.sum_eq_single a]
      · simp
      · intro a' _ ha'
        have hne : f a' ≠ f a := fun h => ha' (hf h)
        simp [hne]
      · simp
    · have hnone : ¬ ∃ a, f a = b := hb
      rw [Function.extend_apply' _ _ _ hnone]
      simp only [pushforward]
      apply Finset.sum_eq_zero
      intro a _
      have hne : f a ≠ b := fun h => hb ⟨a, h⟩
      simp [hne]
  rw [hpushforward]
  exact shannonEntropy_extend_injective hf p

private theorem entropy_pushforward_injective_comp {X A B : Type*}
    [Fintype X] [Fintype A] [Fintype B]
    (p : X -> Real) (f : X -> A) (g : A -> B)
    (hg : Function.Injective g) :
    shannonEntropy (pushforward (g ∘ f) p) =
      shannonEntropy (pushforward f p) := by
  rw [← pushforward_comp]
  exact entropy_pushforward_injective (pushforward f p) g hg

private theorem pushforward_nonnegative {X A : Type*} [Fintype X]
    (p : X -> Real) (f : X -> A) (hp : ∀ x, 0 ≤ p x) :
    ∀ a, 0 ≤ pushforward f p a := by
  classical
  intro a
  simp only [pushforward]
  exact Finset.sum_nonneg fun x _ => by
    by_cases h : f x = a <;> simp [h, hp x]

private def splitLastObservationEquiv (O : Type*) (depth : Nat) :
    (Fin (depth + 2) -> O) ≃ ((Fin (depth + 1) -> O) × O) :=
  (Fin.snocEquiv (fun _ : Fin (depth + 2) => O)).symm.trans
    (Equiv.prodComm O (Fin (depth + 1) -> O))

private theorem split_last_observation_word {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (depth : Nat) (y : Y) :
    splitLastObservationEquiv O depth
        (futureReadoutWord update readout (depth + 1) y) =
      (futureReadoutWord update readout depth y,
        readout ((update^[depth + 1]) y)) := by
  apply Prod.ext
  · funext k
    rfl
  · rfl

private theorem increment_joint_entropy {Y O : Type*}
    [Fintype Y] [Fintype O]
    (update : Y -> Y) (readout : Y -> O) (initial : Y -> Real)
    (depth : Nat) :
    shannonEntropy (observationIncrementJointLaw update readout initial depth) =
      shannonEntropy (observationWordLaw update readout initial (depth + 1)) := by
  let split := splitLastObservationEquiv O depth
  have hmap :
      (fun y =>
        (futureReadoutWord update readout depth y,
          readout ((update^[depth + 1]) y))) =
        split ∘ futureReadoutWord update readout (depth + 1) := by
    funext y
    exact (split_last_observation_word update readout depth y).symm
  rw [observationIncrementJointLaw, observationWordLaw, hmap]
  exact entropy_pushforward_injective_comp initial
    (futureReadoutWord update readout (depth + 1)) split split.injective

private theorem increment_joint_marginal {Y O : Type*}
    [Fintype Y] [Fintype O]
    (update : Y -> Y) (readout : Y -> O) (initial : Y -> Real)
    (depth : Nat) :
    marginal (observationIncrementJointLaw update readout initial depth) =
      observationWordLaw update readout initial depth := by
  classical
  funext word
  simp only [marginal, observationIncrementJointLaw, observationWordLaw, pushforward]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hword : futureReadoutWord update readout depth y = word
  · simp [hword]
  · simp [hword]

private theorem zero_word_entropy {Y O : Type*} [Fintype Y] [Fintype O]
    (update : Y -> Y) (readout : Y -> O) (initial : Y -> Real) :
    shannonEntropy (observationWordLaw update readout initial 0) =
      shannonEntropy (initialReadoutLaw readout initial) := by
  let singletonWord : O ≃ (Fin 1 -> O) := (Equiv.funUnique (Fin 1) O).symm
  have hmap :
      futureReadoutWord update readout 0 = singletonWord ∘ readout := by
    funext y
    apply (Equiv.funUnique (Fin 1) O).injective
    rfl
  rw [observationWordLaw, initialReadoutLaw, hmap]
  exact entropy_pushforward_injective_comp initial readout singletonWord
    singletonWord.injective

private theorem observation_chain_rule {Y O : Type*} [Fintype Y] [Fintype O]
    (update : Y -> Y) (readout : Y -> O) (initial : Y -> Real)
    (hinitial : ∀ y, 0 ≤ initial y) :
    ∀ depth,
      shannonEntropy (observationWordLaw update readout initial depth) =
        shannonEntropy (initialReadoutLaw readout initial) +
          ∑ k ∈ Finset.range depth,
            conditionalEntropy
              (observationIncrementJointLaw update readout initial k) := by
  intro depth
  induction depth with
  | zero =>
      simpa using zero_word_entropy update readout initial
  | succ depth ih =>
      have hjoint_nonnegative :
          ∀ z, 0 ≤ observationIncrementJointLaw update readout initial depth z :=
        pushforward_nonnegative initial
          (fun y =>
            (futureReadoutWord update readout depth y,
              readout ((update^[depth + 1]) y))) hinitial
      have hstep := entropy_chain_rule
        (observationIncrementJointLaw update readout initial depth)
        hjoint_nonnegative
      rw [increment_joint_entropy, increment_joint_marginal] at hstep
      calc
        shannonEntropy (observationWordLaw update readout initial (depth + 1)) =
            shannonEntropy (observationWordLaw update readout initial depth) +
              conditionalEntropy
                (observationIncrementJointLaw update readout initial depth) := hstep
        _ = (shannonEntropy (initialReadoutLaw readout initial) +
              ∑ k ∈ Finset.range depth,
                conditionalEntropy
                  (observationIncrementJointLaw update readout initial k)) +
              conditionalEntropy
                (observationIncrementJointLaw update readout initial depth) := by rw [ih]
        _ = shannonEntropy (initialReadoutLaw readout initial) +
              ∑ k ∈ Finset.range (depth + 1),
                conditionalEntropy
                  (observationIncrementJointLaw update readout initial k) := by
            rw [Finset.sum_range_succ]
            ring

/-- The stable word-completion equivalence sends every realized word to the canonical completion
projection of any state realizing that word. -/
theorem stable_observation_completion_equiv_apply {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (depth : Nat)
    (hstable :
      Setoid.ker (futureReadoutWord update readout depth) =
        Setoid.ker (futureReadoutWord update readout (depth + 1)))
    (y : Y) :
    stableObservationCompletionEquiv update readout depth hstable
        ⟨futureReadoutWord update readout depth y, ⟨y, rfl⟩⟩ =
      completionProjection update readout y := by
  change
    stableCompletionEquiv update readout depth hstable
        ((finiteWordRangeEquiv update readout depth).symm
          ⟨futureReadoutWord update readout depth y, ⟨y, rfl⟩⟩) =
      completionProjection update readout y
  have hrange :
      (finiteWordRangeEquiv update readout depth).symm
          ⟨futureReadoutWord update readout depth y, ⟨y, rfl⟩⟩ =
        (Quotient.mk _ y : PredictionState update readout depth) := by
    apply (finiteWordRangeEquiv update readout depth).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    rfl
  rw [hrange]
  exact ((graded_prediction_shift update readout depth).2.2.2.2 hstable).2.1 y

private theorem stable_completion_entropy {Y O : Type*}
    [Fintype Y] [Fintype O]
    (update : Y -> Y) (readout : Y -> O) (initial : Y -> Real)
    [Fintype (CompletedState update readout)]
    (depth : Nat)
    (hstable :
      Setoid.ker (futureReadoutWord update readout depth) =
        Setoid.ker (futureReadoutWord update readout (depth + 1))) :
    shannonEntropy (pushforward (completionProjection update readout) initial) =
      shannonEntropy (observationWordLaw update readout initial depth) := by
  let word := futureReadoutWord update readout depth
  letI : Fintype (Set.range word) := Fintype.ofFinite (Set.range word)
  let rangeMap : Y -> Set.range word := fun y => ⟨word y, ⟨y, rfl⟩⟩
  let completionEquiv :=
    stableObservationCompletionEquiv update readout depth hstable
  have hcompletion :
      completionProjection update readout = completionEquiv ∘ rangeMap := by
    funext y
    exact (stable_observation_completion_equiv_apply
      update readout depth hstable y).symm
  have hword : word = Subtype.val ∘ rangeMap := rfl
  calc
    shannonEntropy (pushforward (completionProjection update readout) initial) =
        shannonEntropy (pushforward (completionEquiv ∘ rangeMap) initial) := by
          rw [hcompletion]
    _ = shannonEntropy (pushforward rangeMap initial) :=
      entropy_pushforward_injective_comp initial rangeMap completionEquiv
        completionEquiv.injective
    _ = shannonEntropy (pushforward (Subtype.val ∘ rangeMap) initial) :=
      (entropy_pushforward_injective_comp initial rangeMap Subtype.val
        Subtype.val_injective).symm
    _ = shannonEntropy (observationWordLaw update readout initial depth) := by
      rw [← hword]
      rfl

private theorem completion_joint_marginal {Y O : Type*}
    [Fintype Y]
    (update : Y -> Y) (readout : Y -> O) (initial : Y -> Real)
    [Fintype (CompletedState update readout)] :
    marginal (completionObservationJointLaw update readout initial) =
      initialReadoutLaw readout initial := by
  classical
  funext observation
  simp only [marginal, completionObservationJointLaw, initialReadoutLaw, pushforward]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hreadout : readout y = observation
  · simp [hreadout]
  · simp [hreadout]

private theorem completion_joint_entropy {Y O : Type*}
    [Fintype Y] [Fintype O]
    (update : Y -> Y) (readout : Y -> O) (initial : Y -> Real)
    [Fintype (CompletedState update readout)] :
    shannonEntropy (completionObservationJointLaw update readout initial) =
      shannonEntropy (pushforward (completionProjection update readout) initial) := by
  let graph : CompletedState update readout -> O × CompletedState update readout :=
    fun state => (completionReadout update readout state, state)
  have hgraph : Function.Injective graph := by
    intro first second heq
    exact congrArg Prod.snd heq
  have hmap :
      (fun y => (readout y, completionProjection update readout y)) =
        graph ∘ completionProjection update readout := by
    funext y
    rfl
  rw [completionObservationJointLaw, hmap]
  exact entropy_pushforward_injective_comp initial
    (completionProjection update readout) graph hgraph

/-- Every finite observation word satisfies the Shannon chain rule. At an adjacent-partition
stable depth, the canonical realized-word equivalence computes to the completion projection, and
the completion information remaining after the initial readout is exactly the sum of the later
conditional observation entropies. -/
theorem completion_information_chain_decomposition {Y O : Type*}
    [Fintype Y] [Fintype O]
    (update : Y -> Y) (readout : Y -> O) (initial : Y -> Real)
    (hinitial : (∀ y, 0 ≤ initial y) ∧ ∑ y, initial y = 1)
    (stableDepth : Nat)
    (hstable :
      Setoid.ker (futureReadoutWord update readout stableDepth) =
        Setoid.ker (futureReadoutWord update readout (stableDepth + 1))) :
    letI : Fintype (CompletedState update readout) :=
      Fintype.ofFinite (CompletedState update readout)
    (∀ depth,
      shannonEntropy (observationWordLaw update readout initial depth) =
        shannonEntropy (initialReadoutLaw readout initial) +
          ∑ k ∈ Finset.range depth,
            conditionalEntropy
              (observationIncrementJointLaw update readout initial k)) ∧
    (∀ y,
      stableObservationCompletionEquiv update readout stableDepth hstable
          ⟨futureReadoutWord update readout stableDepth y, ⟨y, rfl⟩⟩ =
        completionProjection update readout y) ∧
    conditionalEntropy (completionObservationJointLaw update readout initial) =
      ∑ k ∈ Finset.range stableDepth,
        conditionalEntropy
          (observationIncrementJointLaw update readout initial k) := by
  letI : Fintype (CompletedState update readout) :=
    Fintype.ofFinite (CompletedState update readout)
  have hchain := observation_chain_rule update readout initial hinitial.1
  refine ⟨hchain, ?_, ?_⟩
  · exact stable_observation_completion_equiv_apply
      update readout stableDepth hstable
  · have hjoint_nonnegative :
        ∀ z, 0 ≤ completionObservationJointLaw update readout initial z :=
      pushforward_nonnegative initial
        (fun y => (readout y, completionProjection update readout y)) hinitial.1
    have hcompletion_chain := entropy_chain_rule
      (completionObservationJointLaw update readout initial) hjoint_nonnegative
    rw [completion_joint_entropy,
      stable_completion_entropy update readout initial stableDepth hstable,
      completion_joint_marginal] at hcompletion_chain
    have hword_chain := hchain stableDepth
    linarith

#print axioms completion_information_chain_decomposition

end D5.S3.Entropy.Observation.CompletionInformationChainDecomposition
