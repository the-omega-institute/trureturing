/- GID: D5/S3/ConceptDynamics/Completion/CompletionInformationCost
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Completion/CompletionInformationCost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Completion cost is conditional entropy, which only controls supported fibers. -/

import D5.S3.Entropy.ConditionalEntropyEquality
import D5.S3.Entropy.Forgetting.CapacityMonotone

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'completion_information_cost' D5 Golden/Frozen/accepted` found no hit.
   * The required repository search for `condEntropy`, conditional entropy, chain rules,
     and `H(` found `D5/S3/Entropy/ConditionalEntropy.lean`, whose exact upstream theorem
     `entropy_chain_rule` proves the finite Shannon identity used below.
   * Direct inspection of `ConditionalEntropyEquality.lean` found the exact support-level
     zero characterization and its explicit warning that zero-mass slices are unconstrained.
   * Direct inspection of `DeterministicOutputEntropyRate.lean` found the reusable graph-law
     marginal calculation; the same finite-sum calculation identifies the concept marginal.
   * Pinned-Mathlib searches for `conditionalEntropy`, `conditional_entropy`, `condEntropy`,
     and entropy chain-rule names found no finite real-valued Shannon conditional-entropy API.
   * The main proof therefore applies the repository chain rule and only proves the marginal
     identification. The counterexample uses the upstream support-zero theorem plus `Fin 3`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Completion.CompletionInformationCost

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.ConditionalEntropyEquality
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy

/-- The joint law of a concept readout and a target under a finite source law. -/
noncomputable def completionLaw {X C K : Type*} [Fintype X]
    (mass : X -> ℝ) (concept : X -> C) (target : X -> K) : C × K -> ℝ :=
  pushforward (fun x => (concept x, target x)) mass

/-- The entropy added by adjoining the target is exactly its entropy conditional on the
current concept. -/
theorem completion_information_cost {X C K : Type*}
    [Fintype X] [Fintype C] [Fintype K]
    (mass : X -> ℝ) (concept : X -> C) (target : X -> K)
    (hmass : (forall x, 0 ≤ mass x) ∧ ∑ x, mass x = 1) :
    shannonEntropy (completionLaw mass concept target) -
        shannonEntropy (pushforward concept mass) =
      conditionalEntropy (completionLaw mass concept target) := by
  classical
  have hmarginal :
      marginal (completionLaw mass concept target) = pushforward concept mass := by
    funext c
    simp only [marginal, completionLaw, pushforward]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hconcept : concept x = c
    · simp [hconcept]
    · simp [hconcept]
  have hjoint_nonnegative :
      forall z, 0 <= completionLaw mass concept target z := by
    intro z
    simp only [completionLaw, pushforward]
    exact Finset.sum_nonneg fun x _ => by
      by_cases hpair : (concept x, target x) = z <;> simp [hpair, hmass.1 x]
  have hchain :=
    entropy_chain_rule (completionLaw mass concept target) hjoint_nonnegative
  rw [hmarginal] at hchain
  linarith

/-- Zero conditional entropy need not produce a target factor on the whole source type:
two zero-mass points can share a concept value while carrying different targets. -/
theorem zero_conditional_entropy_not_global_factorization :
    ∃ (mass : Fin 3 -> ℝ) (concept target : Fin 3 -> Bool),
      (forall x, 0 ≤ mass x) ∧ ∑ x, mass x = 1 ∧
      conditionalEntropy (completionLaw mass concept target) = 0 ∧
      (¬ ∃ factor : Bool -> Bool, target = factor ∘ concept) ∧
      ∃ x y, mass x = 0 ∧ mass y = 0 ∧
        concept x = concept y ∧ target x ≠ target y := by
  classical
  let mass : Fin 3 -> ℝ := fun x => if x = 0 then 1 else 0
  let concept : Fin 3 -> Bool := fun _ => false
  let target : Fin 3 -> Bool := fun x => if x = 2 then true else false
  refine ⟨mass, concept, target, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [mass]
    split_ifs <;> norm_num
  · simp [mass]
  · apply conditional_entropy_eq_zero_of_point_mass_on_support
    intro c hc
    refine ⟨false, ?_⟩
    funext k
    fin_cases c <;> fin_cases k
    all_goals
      norm_num [completionLaw, mass, concept, target, pushforward, conditional,
        marginal, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hc
    all_goals
      norm_num [completionLaw, mass, concept, target, pushforward, conditional,
        marginal, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    all_goals simp
  · rintro ⟨factor, hfactor⟩
    have hsame : target (1 : Fin 3) = target (2 : Fin 3) := by
      rw [hfactor]
      rfl
    change false = true at hsame
    exact Bool.false_ne_true hsame
  · refine ⟨1, 2, ?_, ?_, ?_, ?_⟩ <;> simp [mass, concept, target]

example :
    shannonEntropy
          (completionLaw (fun _ : Bool => (1 / 2 : ℝ)) id not) -
        shannonEntropy (pushforward id (fun _ : Bool => (1 / 2 : ℝ))) =
      conditionalEntropy
        (completionLaw (fun _ : Bool => (1 / 2 : ℝ)) id not) := by
  apply completion_information_cost
  constructor
  · intro x
    positivity
  · norm_num [Fintype.sum_bool]

#print axioms completion_information_cost

end D5.S3.ConceptDynamics.Completion.CompletionInformationCost
